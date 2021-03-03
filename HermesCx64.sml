(* Hermes to x86-64 assembler using gcc inline assembler *)
(* uses Linux / System V calling convention: *)

(* parameters (l to r): RDI, RSI, RDX, RCX, R8, R9 *)
(* Return value: RAX *)

(* Caller-saves: R10, R11 *)
(* Callee-saves: RBX, RBP, R12-R15 *)
(* Stack pointer: RSP (growing down) *)

(* 32-bit (low): EAX, ..., R8D, ... *)
(* 16-bit (low): AX, ..., R8W, ... *)
(* 8-bit (low): AL, ..., R8L, ... *)

(* NOTE: RCX is used a scratch register (for shift etc.) *)
(* so parameter 4 (if any) is moved from RCX to R10 and back *)


(* This version: Use register 16 and up and apply register allocation *)


structure HermesCx64 =
struct

  exception Error of string*(int*int)

  val rcx = 2  (* register RCX *)
  val cl = 2   (* register CL (the same, but 8-bit) *)
  val rsp = 7 (* stack pointer register *)
  val rbp = 4 (* frame pointer register *)

  fun newRegister () = x86.newRegister ()

  (* lookup in environment *)
  fun lookup x [] pos =
        raise Error ("undeclared identifier: " ^ x, pos)
    | lookup x ((y,v) :: env) pos =
        if x = y then v else lookup x env pos

  fun fromHex n [] = n
    | fromHex n (c :: cs) =
        if c >= #"0" andalso c <= #"9" then
	  fromHex (n*16 + ord c - ord #"0") cs
	else
	  fromHex (n*16 + ord c - ord #"a" + 10) cs
	  
  fun fromNumString n =
    if String.isPrefix "0x" n then
      fromHex 0 (String.explode (String.extract (n, 2, NONE)))
    else
      Option.getOpt (Int.fromString n, 9999)

  fun signedToString n = (if n<0 then "-" else "") ^ Int.toString (Int.abs n)
  
(* functions used for interfacing Hermes procedure to C *)

  fun cType Hermes.U8 = "uint8_t "
    | cType Hermes.U16 = "uint16_t "
    | cType Hermes.U32 = "uint32_t "
    | cType Hermes.U64 = "uint64_t "
    
  fun scanType Hermes.U8 = "\"%\"SCNu8\""
    | scanType Hermes.U16 = "\"%\"SCNu16\""
    | scanType Hermes.U32 = "\"%\"SCNu32\""
    | scanType Hermes.U64 = "\"%\"SCNu64\""
    
  fun printType Hermes.U8 = "\"0x%\"PRIx8\""
    | printType Hermes.U16 = "\"0x%\"PRIx16\""
    | printType Hermes.U32 = "\"0x%\"PRIx32\""
    | printType Hermes.U64 = "\"0x%\"PRIx64\""

 fun declareArgs [] = "\n"
   | declareArgs (Hermes.VarArg (x, (_, it), _) :: args) =
       "  " ^ cType it ^ "arg_" ^ x ^ ";\n" ^ declareArgs args
   | declareArgs (Hermes.ArrayArg (x, (_, it), _) :: args) =
       "  " ^  cType it ^ "*arg_" ^ x ^ ";\n" ^ declareArgs args

fun readArgs [] = ""
  | readArgs (Hermes.VarArg (x, (_, it), _) :: args) =
      "  scanf(" ^ scanType it ^ "\\n\", &arg_" ^ x ^ ");\n\n" ^ readArgs args
  | readArgs (Hermes.ArrayArg (x, (_, it), _) :: args) =
      "  scanf(\"%[^\\n]%*c\\n\",line);\n" ^
      "  c = line; int sizeOf_" ^ x ^ " = countTokens(line);\n" ^
      "  arg_" ^ x ^ " = (" ^ cType it ^ "*) malloc(sizeof(" ^ cType it ^ ")*sizeOf_" ^ x ^ ");\n" ^
      "  for (i = 0; i < sizeOf_" ^ x ^ "; i++) {\n" ^
      "    while (*c == ' ') c++;\n" ^
      "    sscanf(c, " ^ scanType it ^ "\", &arg_"^ x ^"[i]);\n" ^
      "    while (*c != ' ' && *c != '\\n' && *c != 0) c++;\n" ^
      "  }\n\n" ^  readArgs args


fun printArgs [] = ""
  | printArgs (Hermes.VarArg (x, (_, it), _) :: args) =
      "  printf(" ^ printType it ^ "\\n\", arg_" ^ x ^ ");\n\n" ^ printArgs args
  | printArgs (Hermes.ArrayArg (x, (_, it), _) :: args) =
      "  for (i = 0; i < sizeOf_" ^ x ^ "; i++) {\n" ^
      "    printf(" ^ printType it ^ " \", arg_" ^ x ^"[i]);\n" ^
      "  }\n  printf(\"\\n\");\n\n" ^ printArgs args


fun callArgs [] = ""
  | callArgs [Hermes.VarArg (x, (_, it), _)] = "&arg_" ^ x
  | callArgs [Hermes.ArrayArg (x, (_, it), _)] = "arg_" ^ x
  | callArgs (Hermes.VarArg (x, (_, it), _) :: args) =
      "&arg_" ^ x ^ ", " ^ callArgs args
  | callArgs (Hermes.ArrayArg (x, (_, it), _) :: args) =
      "arg_" ^ x ^ ", " ^ callArgs args
 

(* make C parameter declarations and assign locations to parameters *)
 fun compileCArgs [] = ""
   | compileCArgs [Hermes.VarArg (x, (_, it), _)]  = cType it ^ "*" ^ x
   | compileCArgs [Hermes.ArrayArg (x, (_, it), _)] = cType it ^ "*" ^ x
   | compileCArgs (Hermes.VarArg (x, (_, it), _) :: args) =
       cType it ^ "*" ^ x ^ ", " ^ compileCArgs args 
   | compileCArgs (Hermes.ArrayArg (x, (_, it), _) :: args) =
       cType it ^ "*" ^ x ^ ", " ^ compileCArgs args

(* functions for compiling to x86-64 *)

fun hSize Hermes.U8 = 0
  | hSize Hermes.U16 = 1
  | hSize Hermes.U32 = 2
  | hSize Hermes.U64 = 3

fun size2bytes 0 = 1
  | size2bytes 1 = 2
  | size2bytes 2 = 4
  | size2bytes 3 = 8
  | size2bytes _ = 0

fun translateUop Hermes.Add pos = "add"
  | translateUop Hermes.Sub pos = "sub"
  | translateUop Hermes.XorWith pos = "xor"
  | translateUop Hermes.RoL pos = "rol"
  | translateUop Hermes.RoR pos = "ror"

fun translateBop Hermes.Plus pos = "add"
  | translateBop Hermes.Minus pos = "sub"
  | translateBop Hermes.Times pos = "imul"
  | translateBop Hermes.Xor pos = "xor"
  | translateBop Hermes.BAnd pos = "and"
  | translateBop Hermes.BOr pos = "or"
  | translateBop Hermes.ShiftL pos = "shl"
  | translateBop Hermes.ShiftR pos = "shr"
  | translateBop Hermes.Equal pos = "setne"
  | translateBop Hermes.Less pos = "setae"
  | translateBop Hermes.Greater pos = "setbe"
  | translateBop Hermes.Neq pos = "sete"
  | translateBop Hermes.Leq pos = "seta"
  | translateBop Hermes.Geq pos = "setb"
  | translateBop _ pos = raise Error ("Binop not implemented", pos)

fun isComparison bop =
  List.exists
    (fn cmp => cmp = bop)
    [Hermes.Equal, Hermes.Less, Hermes.Greater,
     Hermes.Neq, Hermes.Leq, Hermes.Geq]

(* create name from position *)
val counter = ref 0

fun makeName prefix (l,p) =
  (counter := (!counter)+1;
   prefix ^ Int.toString l ^ "_" ^ Int.toString p
   ^ "_" ^ signedToString (!counter))

fun compileExp e target env pos0 =
  case e of
    Hermes.Const (n, pos) =>
      [("mov", 3, x86.Constant n, target)]
  | Hermes.Rval (Hermes.Var (x, pos)) =>
      let
        val (t1, loc) = lookup x env pos
	val size = hSize t1
      in
        case (loc, target) of
	  (x86.Register _, _) =>
             [("movz", size, loc, target)]
	| (_, x86.Register _) =>
             [("movz", size, loc, target)]
	| (_, _) =>
	     [("movz", size, loc, x86.Register rcx),
	      ("movz", size, x86.Register rcx, target)]
      end
  | Hermes.Rval (Hermes.Array (x, Hermes.Const (n, p1), pos)) =>
      let
        val (t1, loc) = lookup x env pos
	val size = hSize t1
	val index = fromNumString n
	val offset = signedToString (size2bytes size * index)
      in
        case (loc, target) of
	  (x86.Register r, x86.Register _) =>
            [("movz", size, x86.Offset (r,offset), target)]
	| (x86.Offset (rbp, off), x86.Register _) =>
	    [("mov", 3, loc, x86.Register rcx),
	     ("movz", size, x86.Offset (rcx,offset), target)]
	| (x86.Register r, _) =>
            [("movz", size, x86.Offset (r,offset), x86.Register rcx),
	     ("movz", size, x86.Register rcx, target)]
	| (_, _) =>
	    [("mov", 3, loc, x86.Register rcx),
	     ("movz", size, x86.Offset (rcx,offset), x86.Register rcx),
	     ("movz", size, x86.Register rcx, target)]
      end
  | Hermes.Rval (Hermes.UnsafeArray (x, e, pos)) =>
      compileExp (Hermes.Rval (Hermes.Array (x, e, pos)))
                 target env pos0
  | Hermes.Rval (Hermes.Array (x, e, pos)) =>
      let
        val tmp = newRegister ()
        val (t1, loc) = lookup x env pos
        val size = hSize t1
	val scale = signedToString (size2bytes size)
        val code1 = compileExp e (x86.Register tmp) env pos
      in
        code1 @
	(if scale = "1" then
	   case (loc, target) of
	     (x86.Register r1, x86.Register r2) =>
               [("movz", size, x86.ROffset (r1,tmp), target)]
	   | (x86.Register r1, _) =>
               [("movz", size, x86.ROffset (r1,tmp), x86.Register rcx),
                ("movz", size, x86.Register rcx, target)]
	   | (_, x86.Register r2) =>
               [("mov", 3, loc, x86.Register rcx),
                ("movz", size, x86.ROffset (rcx,tmp), target)]
	   | (_, _) =>
               [("mov", 3, loc, x86.Register rcx),
                ("movz", size, x86.ROffset (rcx,tmp), x86.Register rcx),
                ("movz", size, x86.Register rcx, target)]
	 else
	   case (loc, target) of
	     (x86.Register r1, x86.Register r2) =>
               [("movz", size, x86.Scaled (r1,tmp,scale), target)]
	   | (x86.Register r1, _) =>
               [("movz", size, x86.Scaled (r1,tmp,scale), x86.Register rcx),
                ("movz", size, x86.Register rcx, target)]
	   | (_, x86.Register r2) =>
               [("mov", 3, loc, x86.Register rcx),
                ("movz", size, x86.Scaled (rcx,tmp,scale), target)]
	   | (_, _) =>
               [("mov", 3, loc, x86.Register rcx),
                ("movz", size, x86.Scaled (rcx,tmp,scale), x86.Register rcx),
                ("movz", size, x86.Register rcx, target)])
      end
  | Hermes.Un (Hermes.Negate, e1, pos) =>
      compileExp e1 target env  pos @
      [("not", 3, target, x86.NoOperand)]
  | Hermes.Bin (bop, e1, Hermes.Const (n, p1), pos) =>
      let
        val code1 = compileExp e1 target env pos
        val opcode = translateBop bop pos
	val hNum = BigInt.string2h n pos
	val maxImm = BigInt.string2h "0x7fffffff" pos
      in
        if BigInt.hGeq64 maxImm hNum then (* fits in immediate *)
          if isComparison bop
          then
            code1 @
            [("cmp", 3, x86.Constant n, target),
             (opcode, 0, target, x86.NoOperand),
             ("sub", 3, x86.Constant "1", target)]
          else
            code1 @
            [(opcode, 3, x86.Constant n, target)]
	else (* too big for immediate *)
	  if isComparison bop
          then
            code1 @
            [("mov", 3, x86.Constant n, x86.Register rcx),
	     ("cmp", 3, x86.Register rcx, target),
             (opcode, 0, target, x86.NoOperand),
             ("sub", 3, x86.Constant "1",  target)]
          else
            code1 @
            [("mov", 3, x86.Constant n, x86.Register rcx),
	     (opcode, 3, x86.Register rcx, target)]
      end
  | Hermes.Bin (bop, e1, Hermes.Rval (Hermes.Var (x, p1)), pos) =>
      let
        val (t1, loc) = lookup x env p1
	val size = hSize t1
        val code1 = compileExp e1 target env pos
        val opcode = translateBop bop pos
      in
        if isComparison bop andalso size = 3
	 then
	   code1 @
	   (case (loc,target) of
	      (x86.Register r1, _) =>
	        [("cmp", 3, loc, target),
	         (opcode, 0, target, x86.NoOperand),
	         ("sub", 3, x86.Constant "1", target)]
	    | (_, x86.Register r1) =>
	        [("cmp", 3, loc, target),
	         (opcode, 0, target, x86.NoOperand),
	         ("sub", 3, x86.Constant "1", target)]
	    | (_, _) =>
	        [("mov", 3, loc, x86.Register rcx),
	         ("cmp", 3, x86.Register rcx, target),
	         (opcode, 0, target, x86.NoOperand),
	         ("sub", 3, x86.Constant "1", target)])
        else if isComparison bop andalso size < 3
	 then
	   code1 @
	   [("movz", size, loc, x86.Register rcx),
	    ("cmp", 3, x86.Register rcx, target),
	    (opcode, 0, target, x86.NoOperand),
	    ("sub", 3, x86.Constant "1", target)]
	 else if opcode = "shl" orelse opcode = "shr"
        then (* move shift counter to RCX *)
          code1 @
          [("mov", 0, loc, x86.Register cl),
	   (opcode, 3, x86.Register cl, target)]
        else
          code1 @
	   (case (loc,target) of
	     (x86.Register r1, _) =>
                [(opcode, 3, loc, target)]
	   | (_, x86.Register r1) =>
                [(opcode, 3, loc, target)]
	   | (_, _) =>
                [("mov", 3, loc, x86.Register rcx),
		 (opcode, 3, x86.Register rcx, target)])
      end
  | Hermes.Bin (bop, e1, e2, pos) =>
           let
	     val tmp = newRegister ()
	     val code1 = compileExp e1 target env pos
	     val code2 = compileExp e2 (x86.Register tmp) env pos
	     val opcode = translateBop bop pos
	   in
      	     if isComparison bop then
	       code1 @ code2 @
	       [("cmp", 3, x86.Register tmp, target),
	        (opcode, 0, target, x86.NoOperand),
	        ("sub", 3, x86.Constant "1", target)]
	     else if opcode = "shl" orelse opcode = "shr"
	     then
	       code1 @ code2 @
	       [("mov", 0, x86.Register tmp, x86.Register cl),
	        (opcode, 3, x86.Register cl, target)]
	     else
	       code1 @ code2 @
	       [(opcode, 3, x86.Register tmp, target)]
	   end
  | Hermes.AllZero (x, exp, pos) =>
      (case exp of
         Hermes.Const (n, p1) =>
 	   let
	     val (t, loc) = lookup x env p1
	     val (r, code0) =
	       case loc of
                 x86.Register r => (r, [])
	       | _ => let val tmp = newRegister ()
	              in (tmp, [("mov", 3, loc, x86.Register tmp)]) end
	     val size = hSize t
	     val arraySize = fromNumString n
	     val orCode =
	           List.tabulate
		     (arraySize,
		      fn i => ("or", size,
		  	       x86.Offset
			         (r, signedToString (size2bytes size * i)),
			       x86.Register rcx))
	   in
	     code0 @
	     [("mov", size, x86.Constant "0", x86.Register rcx)]
	     @ orCode @ (* doesn't set flags if array size is 0 *)
	     [("setne", 0, target, x86.NoOperand),
	      ("sub", 3, x86.Constant "1", target)]
	   end
      | _ => raise Error ("Array size should be constant after PE", pos))
  | e => raise Error (Hermes.showExp e false ^ " not implemented", pos0)


(* allocate local variables in registers *)
fun compileDecs1 [] env = ([], env)
  | compileDecs1 (Hermes.ConstDecl (_,_,pos) :: ds) env =
      raise Error ("constants should have been eliminated by PE", pos)
  | compileDecs1 (Hermes.VarDecl (x,(_,it),pos) :: ds) env =
            let
	      val r = newRegister ()
	      val env1 = (x,(it,x86.Register r)) :: env
	      val (code1, env2) = compileDecs1 ds env1
	    in
	      ([("xor", 3, x86.Register r, x86.Register r)] (* clear *)
	       @ code1,
	       env2)
	    end
  | compileDecs1 (Hermes.ArrayDecl (x,(_,it), exp, pos) :: ds) env =
      (case exp of
         Hermes.Const (n, p1) =>
            let
	      val r = newRegister ()
	      val env1 = (x,(it,x86.Register r)) :: env
	      val size = hSize it
	      val arraySize = fromNumString n
	      val arraySize2 = signedToString (size2bytes size * arraySize)
	      val (code1, env2) = compileDecs1 ds env1
	      val clearCode =
	            List.tabulate
		      (arraySize,
		       fn i => ("mov", size,
		                x86.Constant "0",
				x86.Offset
				  (r, signedToString (size2bytes size * i))))
	    in
	      ([("sub", 3, x86.Constant arraySize2, x86.Register rsp),
	        ("mov", 3, x86.Register rsp, x86.Register r)]
	       @ clearCode @ code1,
	       env2)
	    end
       | _ => raise Error ("Array size should be constant after PE", pos))
	    
  
fun compileDecs2 [] env = []
  | compileDecs2 (Hermes.ConstDecl (_,_,pos) :: ds) env =
      raise Error ("constants should have been eliminated by PE", pos)
  | compileDecs2 (Hermes.VarDecl (x,(_,it),pos) :: ds) env =
            let
	      val r = newRegister ()
	      val env1 = (x,(it,x86.Register r)) :: env
	      val code1 = compileDecs2 ds env1
	    in
	      code1
	    end
  | compileDecs2 (Hermes.ArrayDecl (x,(_,it), exp, pos) :: ds) env =
      (case exp of
         Hermes.Const (n, p1) =>
            let
	      val r = newRegister ()
	      val env1 = (x,(it,x86.Register r)) :: env
	      val size = hSize it
	      val arraySize = fromNumString n
	      val arraySize2 = signedToString (size2bytes size * arraySize)
	      val code1 = compileDecs2 ds env1
	    in
	      code1 @
	      [("add", 3, x86.Constant arraySize2, x86.Register rsp)]
	    end
       | _ => raise Error ("Array size should be constant after PE", pos))
	    
  

fun compileStat stat env =
  (case stat of
    Hermes.Skip => []
  | Hermes.Update (uop, Hermes.Var (x, p1), Hermes.Const (n, p2), pos) =>
      let
        val (t1, loc) = lookup x env p1
        val size = hSize t1
	val bits = 8 * size2bytes size
	val opc = translateUop uop pos
	val hNum = BigInt.string2h n pos
	val hNumSized = BigInt.limitZ bits hNum
	val n1 = BigInt.h2hString  hNumSized
	val maxImm = BigInt.string2h "0x7fffffff" pos
      in
        if BigInt.hGeq64 maxImm hNumSized then (* fits in immediate *)
          [(opc, size, x86.Constant n1, loc)]
	else
          [("mov", size, x86.Constant n1, x86.Register rcx),
	   (opc, size, x86.Register rcx,  loc)]
      end
  | Hermes.Update (uop, Hermes.Var (x, p1),
                        Hermes.Rval (Hermes.Var (y, p2)), pos) =>
      let
        val (t1, loc1) = lookup x env p1
        val (t2, loc2) = lookup y env p2
        val size = hSize t1 (* t1 == t2 *)
	val opc = translateUop uop pos
      in
        if opc = "rol" orelse opc = "ror" then
	  [("mov", 0, loc2, x86.Register rcx),
	   (opc, size, x86.Register rcx,  loc1)]
	else
	  case (loc1, loc2) of
	    (x86.Register _, _) =>
              [(opc, size, loc2, loc1)]
	  | (_, x86.Register _) =>
              [(opc, size, loc2, loc1)]
	  | (_,  _) =>
              [("mov", size, loc2, x86.Register rcx),
	       (opc, size, x86.Register rcx, loc1)]
      end
  | Hermes.Update (uop, Hermes.Var (x, p1), e, pos) =>
          let
	     val tmp = newRegister ()
            val (t1, loc) = lookup x env p1
            val size = hSize t1
	    val opc = translateUop uop pos
	    val eCode = compileExp e (x86.Register tmp) env pos
          in
	    eCode @
            (if opc = "rol" orelse opc = "ror" then
	       [("mov", 0, x86.Register tmp, x86.Register rcx),
	        (opc, size, x86.Register rcx, loc)]
	     else
 	       [(opc, size, x86.Register tmp, loc)])
          end
  | Hermes.Update (uop, Hermes.Array (x, Hermes.Const (n, p2), p1), e, pos) =>
          let
	    val tmp = newRegister ()
            val (t1, loc) = lookup x env p1
	    val size = hSize t1
	    val opc = translateUop uop pos
	    val index = fromNumString n
	    val offset = signedToString (size2bytes size * index)
	    val eCode = compileExp e (x86.Register tmp) env pos
          in
	    eCode @
	    (case loc of
	       x86.Register r1 =>
                (if opc = "rol" orelse opc = "ror" then
	           [("mov", 0, x86.Register tmp, x86.Register rcx),
	            (opc, size, x86.Register rcx,  x86.Offset (r1, offset))]
	         else
	           [(opc, size, x86.Register tmp,  x86.Offset (r1, offset))])
	    | _ =>
                (if opc = "rol" orelse opc = "ror" then
	           [("mov", 0, x86.Register tmp, x86.Register rcx),
	            ("mov", 3, loc, x86.Register tmp),
	            (opc, size, x86.Register rcx,  x86.Offset (tmp, offset))]
	         else
	           [("mov", 3, loc, x86.Register rcx),
	            (opc, size, x86.Register tmp,  x86.Offset (rcx, offset))]))
          end
  | Hermes.Update (uop, Hermes.UnsafeArray (x, e1, p1), e2, pos) =>
      compileStat (Hermes.Update (uop, Hermes.Array (x, e1, p1), e2, pos))
                  env
  | Hermes.Update (uop, Hermes.Array (x, e1, p1), e2, pos) =>
          let
	    val tmp1 = newRegister ()
	    val tmp2 = newRegister ()
            val (t1, loc) = lookup x env p1
	    val size = hSize t1
	    val scale = signedToString (size2bytes size)
	    val opc = translateUop uop pos
	    val e1Code = compileExp e1 (x86.Register tmp1) env pos
	    val e2Code = compileExp e2 (x86.Register tmp2) env pos
          in
	    e1Code @ e2Code @
	    (case loc of
	       x86.Register r1 =>
                (if opc = "rol" orelse opc = "ror" then
	           [("mov", 0, x86.Register tmp2, x86.Register rcx),
	            (opc, size, x86.Register rcx,
		     if scale = "1" then x86.ROffset (r1, tmp1)
		     else x86.Scaled (r1, tmp1, scale))]
	         else
	           [(opc, size, x86.Register tmp2,
		     if scale = "1" then x86.ROffset (r1, tmp1)
	             else x86.Scaled (r1, tmp1, scale))])
	     | _ =>
                (if opc = "rol" orelse opc = "ror" then
	           [("mov", 0, x86.Register tmp2, x86.Register rcx),
	            ("mov", 3, loc, x86.Register tmp2),
	            (opc, size, x86.Register rcx,
		     if scale = "1" then x86.ROffset (tmp2, tmp1)
		     else x86.Scaled (tmp2, tmp1, scale))]
	         else
	           [("mov", 3, loc, x86.Register rcx),
	            (opc, size, x86.Register tmp2,
		     if scale = "1" then x86.ROffset (rcx, tmp1)
	             else x86.Scaled (rcx, tmp1, scale))]))
          end
  
  | Hermes.Swap (Hermes.Var (x, p1), Hermes.Var (y, p2), pos) =>
      let
        val (t1, loc1) = lookup x env p1
        val (t2, loc2) = lookup y env p2 (* t1==t2 by types *)
	val size = hSize t1
	val r2 = newRegister ()
      in
        case (loc1, loc2) of
	  (x86.Register r1, _) =>
            [("movz", size,  loc2, x86.Register rcx),
             ("mov", size, loc1, loc2),
             ("movz", size,  x86.Register rcx,  loc1)]
	 | (_, x86.Register r2) =>
            [("movz", size,  loc1, x86.Register rcx),
             ("mov", size, loc2, loc1),
             ("movz", size,  x86.Register rcx,  loc2)]
	| _ =>
                 [("mov", size, loc1, x86.Register rcx),
                  ("mov", size, loc2, x86.Register r2),
                  ("mov", size, x86.Register rcx, loc2),
                  ("mov", size, x86.Register r2,  loc1)]
      end
  | Hermes.Swap (Hermes.Var (x, p1),
                 Hermes.Array (y, Hermes.Const (n, p3), p2), pos) =>
      let
        val (t1, loc1) = lookup x env p1
        val (t2, loc2) = lookup y env p2 (* t1==t2 by types *)
	val size = hSize t1
	val index = fromNumString n
	val offset = signedToString (size2bytes size * index)
	val r1 = newRegister ()
	val r2 = newRegister ()
      in
        case (loc1, loc2) of
	  (x86.Register r1, x86.Register r2) =>
            [("movz", size, x86.Offset (r2, offset),  x86.Register rcx),
             ("mov", size, x86.Register r1, x86.Offset (r2, offset)),
             ("movz", size, x86.Register rcx,  x86.Register r1)]
	| (_, x86.Register r3) =>
                 [("movz", size, x86.Offset (r3, offset),  x86.Register rcx),
		  ("movz", size, loc1, x86.Register r1),
                  ("mov", size, x86.Register r1, x86.Offset (r3, offset)),
                  ("mov", size, x86.Register rcx,  loc1)]
	| (_, _) =>
                 [("mov", 3, loc2, x86.Register r2),
		  ("movz", size, x86.Offset (r2, offset),  x86.Register rcx),
		  ("movz", size, loc1, x86.Register r1),
                  ("mov", size, x86.Register r1, x86.Offset (r2, offset)),
                  ("mov", size, x86.Register rcx,  loc1)]
      end
  | Hermes.Swap (Hermes.Array (y, Hermes.Const (n, p3), p2),
                 Hermes.Var (x, p1), pos) =>
      compileStat
        (Hermes.Swap (Hermes.Var (x, p1),
                      Hermes.Array (y, Hermes.Const (n, p3), p2), pos))
	env
  | Hermes.Swap (Hermes.Array (x, Hermes.Const (m, p3), p1),
                 Hermes.Array (y, Hermes.Const (n, p4), p2), pos) =>
      let
        val (t1, loc1) = lookup x env p1
        val (t2, loc2) = lookup y env p2 (* t1==t2 by types *)
	val size = hSize t1
	val index1 = fromNumString m
	val offset1 = signedToString (size2bytes size * index1)
	val index2 = fromNumString n
	val offset2 = signedToString (size2bytes size * index2)
	val tmp = newRegister ()
	val tmp1 = newRegister ()
	val tmp2 = newRegister ()
	val tmp3 = newRegister ()
      in
        case (loc1, loc2) of
	  (x86.Register r1, x86.Register r2) =>
	         [("movz", size, x86.Offset (r1, offset1), x86.Register rcx),
	          ("movz", size, x86.Offset (r2, offset2), x86.Register tmp),
	          ("mov", size, x86.Register rcx, x86.Offset (r2, offset2)),
	          ("mov", size, x86.Register tmp, x86.Offset (r1, offset1))]
	| (x86.Register r1, loc2) =>
	         [("movz", size, x86.Offset (r1, offset1), x86.Register rcx),
		  ("mov", 3, loc2, x86.Register tmp2),
	          ("movz", size, x86.Offset (tmp2, offset2), x86.Register tmp1),
	          ("mov", size, x86.Register rcx, x86.Offset (tmp2, offset2)),
	          ("mov", size, x86.Register tmp1, x86.Offset (r1, offset1))]
	| (loc1, x86.Register r1) =>
	         [("movz", size, x86.Offset (r1, offset1), x86.Register rcx),
		  ("mov", 3, loc1, x86.Register tmp2),
	          ("movz", size, x86.Offset (tmp2, offset1), x86.Register tmp1),
	          ("mov", size, x86.Register rcx, x86.Offset (tmp2, offset1)),
	          ("mov", size, x86.Register tmp1, x86.Offset (r1, offset2))]
	 | (loc1, loc2) =>
	         [("mov", 3, loc1, x86.Register tmp1),
	          ("mov", 3, loc2, x86.Register tmp1),
		  ("movz", size, x86.Offset (tmp1, offset1), x86.Register rcx),
	          ("movz", size, x86.Offset (tmp2, offset2), x86.Register tmp3),
	          ("mov", size, x86.Register rcx, x86.Offset (tmp2, offset2)),
	          ("mov", size, x86.Register tmp3, x86.Offset (tmp1, offset1))]
      end
  | Hermes.Swap (Hermes.UnsafeArray (y, e, p2), lv, pos) =>
      compileStat (Hermes.Swap (Hermes.Array (y, e, p2), lv, pos)) env
  | Hermes.Swap (lv, Hermes.UnsafeArray (y, e, p2), pos) =>
      compileStat (Hermes.Swap (lv, Hermes.Array (y, e, p2), pos)) env
  
  | Hermes.CondSwap (e, Hermes.Var (x, p1), Hermes.Var (y, p2), pos) =>
        let
	  val tmp1 = newRegister ()
          val (t1, loc1) = lookup x env p1
          val (t2, loc2) = lookup y env p2 (* t1==t2 by types *)
	  val size = hSize t1
	  val code1 = (* tmp1 := e as all 0 or all 1 *)
	    compileExp e (x86.Register tmp1) env pos @
	    [("sete", 0, x86.Register tmp1, x86.NoOperand),
	     ("sub", 3, x86.Constant "1", x86.Register tmp1)]
	  val code2 = (* rcx := tmp1 & (x ^ y) *)
	    [("mov", size, loc1, x86.Register rcx),
	     ("xor", size, loc2, x86.Register rcx),
	     ("and", size, x86.Register tmp1, x86.Register rcx)]
        in
	  code1 @ code2 @
	  [("xor", size, x86.Register rcx, loc1),
	   ("xor", size, x86.Register rcx, loc2)]
        end
  | Hermes.CondSwap (e,
    		     Hermes.Var (x, p1),
                     Hermes.Array (y, Hermes.Const (n, p3), p2), pos) =>
        let
	  val tmp1 = newRegister ()
	  val tmp2 = newRegister ()
          val (t1, loc1) = lookup x env p1
          val (t2, loc2) = lookup y env p2 (* t1==t2 by types *)
	  val size = hSize t1
  	  val index = fromNumString n
 	  val offset = signedToString (size2bytes size * index)
	  val code1 =
	    compileExp e (x86.Register tmp1) env pos @
	    [("sete", 0, x86.Register tmp1, x86.NoOperand),
	     ("sub", 3, x86.Constant "1", x86.Register tmp1)]
	  val code2 =
	    [("mov", 3, loc2, x86.Register rcx),
	     ("mov", size, x86.Offset (rcx, offset), x86.Register tmp2),
	     ("xor", size, loc1, x86.Register tmp2),
	     ("and", size, x86.Register tmp1, x86.Register tmp2)]
        in
	  code1 @ code2 @
	  [("xor", size, x86.Register tmp2, loc1),
	   ("xor", size, x86.Register tmp2, x86.Offset (rcx, offset))]
        end
  | Hermes.CondSwap (e,
    		     Hermes.Array (y, Hermes.Const (n, p3), p2),
                     Hermes.Var (x, p1), pos) =>
      compileStat
        (Hermes.CondSwap (e,
			  Hermes.Var (x, p1),
                          Hermes.Array (y, Hermes.Const (n, p3), p2), pos))
	env
  | Hermes.CondSwap (e,
    		     Hermes.Array (x, Hermes.Const (m, p3), p1),
                     Hermes.Array (y, Hermes.Const (n, p4), p2), pos) =>
        let
	  val tmp1 = newRegister ()
	  val tmp2 = newRegister ()
	  val tmp3 = newRegister ()
          val (t1, loc1) = lookup x env p1
          val (t2, loc2) = lookup y env p2 (* t1==t2 by types *)
	  val size = hSize t1
  	  val index1 = fromNumString m
 	  val offset1 = signedToString (size2bytes size * index1)
  	  val index2 = fromNumString n
 	  val offset2 = signedToString (size2bytes size * index2)
	  val code1 =
	    compileExp e (x86.Register tmp1) env pos @
	    [("sete", 0, x86.Register rcx, x86.NoOperand),
	     ("sub", 3, x86.Constant "1", x86.Register rcx)]
	  val code2 =
	    [("mov", 3, loc1, x86.Register tmp1),
	     ("mov", size, x86.Offset (tmp1, offset1), x86.Register tmp2),
	     ("mov", 3, loc2, x86.Register tmp3),
	     ("xor", size, x86.Offset (tmp3, offset2), x86.Register tmp2),
	     ("and", size, x86.Register rcx, x86.Register tmp2)]
        in
	  code1 @ code2 @
	  [("xor", size, x86.Register tmp2,  x86.Offset (tmp1, offset1)),
	   ("xor", size, x86.Register tmp2, x86.Offset (tmp3, offset2))]
        end
  
  | Hermes.CondSwap (c, Hermes.UnsafeArray (y, e, p2), lv, pos) =>
      compileStat (Hermes.CondSwap (c, Hermes.Array (y, e, p2), lv, pos))
                  env
  | Hermes.CondSwap (c, lv, Hermes.UnsafeArray (y, e, p2), pos) =>
      compileStat (Hermes.CondSwap (c, lv, Hermes.Array (y, e, p2), pos))
                  env
  | Hermes.Block (ds, ss, p) =>
      let
        val (code1, env1) = compileDecs1 ds env
        val ssCode = List.map (fn s => compileStat s env1) ss
        val code2 = compileDecs2 ds env
      in
        code1 @ List.concat ssCode @ code2
      end
      
  | Hermes.Assert (Hermes.Bin (Hermes.Equal,
                               Hermes.Rval (Hermes.Var (x,p1)),
			       Hermes.Const ("0x0",p2), p3),
	           (l,p)) =>
      let
        val (t1, loc1) = lookup x env p1
	val size = hSize t1
	val label = makeName "label" (l,p)
      in
	[("cmp", size, x86.Constant "0", loc1),
	 ("je " ^ label, 9, x86.NoOperand, x86.NoOperand),

	 ("mov", 3, x86.Constant (signedToString (10000*l+p)),
	            x86.Offset (rbp, "-102")),
	 ("jmp exit_label_", 9, x86.NoOperand, x86.NoOperand),
	 (label ^ ":", 9, x86.NoOperand, x86.NoOperand)]
      end        
  | Hermes.Assert (e, (l,p)) =>
	    let
	      val tmp = newRegister ()
	      val eCode = compileExp e (x86.Register tmp) env (l,p)
	      val label = makeName "label" (l,p)
	    in
	      eCode @
	      [("cmp", 3, x86.Constant "0", x86.Register tmp),
	       ("jne " ^ label, 9, x86.NoOperand, x86.NoOperand),

	       ("mov", 3, x86.Constant (signedToString (10000*l+p)),
	                  x86.Offset (rbp, "-102")),
	       ("jmp exit_label_", 9, x86.NoOperand, x86.NoOperand),
	       (label ^ ":", 9, x86.NoOperand, x86.NoOperand)]
	    end
  | s => raise Error ("Not implemented: " ^ Hermes.showStat s, (0,0)))


fun setMinus [] ys = []
  | setMinus (x :: xs) ys =
      if List.exists (fn y => x=y) ys
      then setMinus xs ys
      else x :: setMinus xs ys

(* move parameters to and from pseudo registers *)
fun compileX86Args [] locs = ([], [], [])
   | compileX86Args _ [] =
       raise Error ("Not enough parameter locations", (0,0))
   | compileX86Args (Hermes.VarArg (x, (_, it), _) :: args) (l1 :: locs) =
       let
         val (env, code0, code1) = compileX86Args args locs
	 val r = newRegister ()
	 val r1 = newRegister ()
       in
      	 ((x,(it,x86.Register r)) :: env,
	  [("mov", 3, l1, x86.Register r1),
	   ("mov", 3, x86.Indirect r1, x86.Register r)]
	   @ code0,
	   code1 @
	   [("mov", 3, x86.Register r, x86.Indirect r1),
	    ("mov", 3, x86.Register r1, l1)])
       end
   | compileX86Args (Hermes.ArrayArg (x, (_, it), _) :: args) (l1 :: locs) =
       let
         val (env, code0, code1) = compileX86Args args locs
	 val r = newRegister ()
       in
      	     ((x,(it,x86.Register r)) :: env,
	      [("mov", 3, l1, x86.Register r)]
	      @ code0,
	      code1 @
	      [("mov", 3, x86.Register r, l1)])
       end

fun replace999 [] offset = [] (* should not happen *)
  | replace999 (("lea", 3, x86.Offset (4, "-999"), x86.Register 7) :: instrs)
               offset =
	(("lea", 3, x86.Offset (4, offset), x86.Register 7) :: instrs)
  | replace999 (instr :: instrs) offset =
        instr :: replace999 instrs offset

fun compileProcedure f args body =
  let
    val parameterLocations =
      List.map x86.Register x86.argRegs @
      List.map (fn n => x86.Offset(rbp, signedToString n))
               [16,24,32,40,48]
    val arglist = compileCArgs args
    val (env, prologue1, epilogue0) = compileX86Args args parameterLocations
    val prologue2 = (* save callee-saves variables *)
          [("mov", 3, x86.Register 1, x86.Offset (rbp, "-54")),
	   ("mov", 3, x86.Register 12, x86.Offset (rbp, "-62")),
	   ("mov", 3, x86.Register 13, x86.Offset (rbp, "-70")),
	   ("mov", 3, x86.Register 14, x86.Offset (rbp, "-78")),
	   ("mov", 3, x86.Register 15, x86.Offset (rbp, "-86")),
	   ("mov", 3, x86.Register rsp, x86.Offset (rbp, "-94")),
	   ("mov", 3, x86.Constant "0", x86.Offset (rbp, "-102")),
	   ("lea", 3, x86.Offset (rbp, "-999"), x86.Register rsp)]
    val bodyCode = compileStat body env
    val epilogue1 =
          [("exit_label_:", 9, x86.NoOperand, x86.NoOperand),
	   ("mov", 3,  x86.Offset (rbp, "-102"), x86.Register 0)]
    val epilogue2 = (* restore callee-saves variables *)
          [("mov", 3, x86.Offset (rbp, "-54"), x86.Register 1),
	   ("mov", 3, x86.Offset (rbp, "-62"), x86.Register 12),
	   ("mov", 3, x86.Offset (rbp, "-70"), x86.Register 13),
	   ("mov", 3, x86.Offset (rbp, "-78"), x86.Register 14),
	   ("mov", 3, x86.Offset (rbp, "-86"), x86.Register 15),
	   ("mov", 3, x86.Offset (rbp, "-94"), x86.Register rsp)]
    val epilogue3 = [("xor", 3, x86.Register 10, x86.Register 10),
    		     ("xor", 3, x86.Register 11, x86.Register 11)]
    val allCode =
          prologue1 @ prologue2 @ bodyCode @
	  epilogue0 @ epilogue1 @ epilogue2 @ epilogue3
    val (newCode, offset) = x86.registerAllocate allCode
    val newCode1 = replace999 newCode (signedToString offset)
  in
    "int " ^ f ^ "(" ^ arglist ^ ")\n" ^
    "{\n  asm volatile ( \n" ^
    String.concat (List.map x86.printInstruction newCode1) ^
    "  );\n}\n\n"
  end


end