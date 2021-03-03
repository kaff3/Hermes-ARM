(* x86-64 instruction subset *)
(* Assumes Linux / System V calling convention *)

(* parameters (l to r): RDI, RSI, RDX, RCX, R8, R9 *)
(* Return value: RAX *)
(* Caller-saves: R10, R11 *)
(* Callee-saves: RBX, RBP, R12-R15 *)
(* Frame pointer pointer: RBP *)
(* Stack pointer: RSP (growing down) *)

(* 32-bit (low): EAX, ..., R8D, ... *)
(* 16-bit (low): AX, ..., R8W, ... *)
(* 8-bit (low): AL, ..., R8L, ... *)


structure x86 =
struct

  exception Error of string
  
  (* Number, 8-bit name, 16-bit name, 32-bit name, 64-bit name *)
  val regs = [["al", "ax", "eax", "rax"], (* 0 *)
              ["bl", "bx", "ebx", "rbx"], (* 1 *)
              ["cl", "cx", "ecx", "rcx"], (* 2 *)
              ["dl", "dx", "edx", "rdx"], (* 3 *)
              ["bpl", "bp", "ebp", "rbp"], (* 4 *)
              ["sil", "si", "esi", "rsi"], (* 5 *)
              ["dil", "di", "edi", "rdi"], (* 6 *)
              ["spl", "sp", "esp", "rsp"], (* 7 *)
              ["r8b", "r8w", "r8d", "r8"],
              ["r9b", "r9w", "r9d", "r9"],
              ["r10b", "r10w", "r10d", "r10"],
              ["r11b", "r11w", "r11d", "r11"],
              ["r12b", "r12w", "r12d", "r12"],
              ["r13b", "r13w", "r13d", "r13"],
              ["r14b", "r14w", "r14d", "r14"],
              ["r15b", "r15w", "r15d", "r15"]]
	      @ (* and pseudo registers *)
	      List.tabulate
	        (32, fn i => let val r = Int.toString (i+16)
		             in ["p"^r^"b","p"^r^"w","p"^r^"d","p"^r] end)

  val argRegs = [6, 5, 3, 2, 8, 9]
  val returnReg = 0
  val callerSaves = [10, 11]
  val calleeSaves = [1, 12, 13, 14, 15]
  val stackP = 7
  val rbp = 4

  datatype operand = Register of int
                   | Constant of string
		   | Indirect of int (* address in register *)
		   | Offset of int * string (* adresss = register + const *)
		   | ROffset of int * int (* adresss = register + register *)
		   | Scaled of int * int * string
		       (* adresss = register + register*scale *)
		   | NoOperand

  fun printOperand size (Register r) =
         "%" ^ (List.nth (List.nth (regs,r),size))
    | printOperand size (Constant n) = "$" ^ n
    | printOperand size (Indirect r) =
         "(" ^ printOperand 3 (Register r) ^ ")"
    | printOperand size (Offset (r, "0")) =
         "(" ^ printOperand 3 (Register r) ^ ")"
    | printOperand size (Offset (r, n)) =
         n ^ "(" ^ printOperand 3 (Register r) ^ ")"
    | printOperand size (ROffset (r1, r2)) =
         "(" ^ printOperand 3 (Register r1) ^ ", " ^
	 printOperand 3 (Register r2) ^ ")"
    | printOperand size (Scaled (r1, r2, scale)) =
         "(" ^ printOperand 3 (Register r1) ^ ", " ^
	 printOperand 3 (Register r2) ^ ", " ^ scale ^ ")"
    | printOperand size NoOperand = ""

  (* string is opcode without size suffix *)
  (* int = 0: 8-bit, 1: 16-bit, 2: 32-bit, 3: 64 bit *)
  type instruction = string * int * operand * operand

  fun printInstruction ("movz", size, op1, op2) =
        let
          val sizedOpcode = case size of
                              0 => "movzbq"
	                    | 1 => "movzwq"
	                    | 2 => "movl"
			    | _ => "movq"
          val operand1 = printOperand size op1
          val operand2 = printOperand (if size = 2 then 2 else 3) op2
        in
          "        \"" ^ sizedOpcode ^ "  " ^ operand1 ^
	  ", " ^ operand2 ^ "\\n\\t\"\n"
        end
    | printInstruction (opcode, size, op1, op2) =
        let
          val sizedOpcode = case size of
                              0 => opcode ^ "b"
	                    | 1 => opcode ^ "w"
		   	    | 2 => opcode ^ "l"
			    | 3 => opcode ^ "q"
			    | _ => opcode
          val operand1 =
            if opcode = "shr" orelse opcode = "shl" orelse
	       opcode = "ror" orelse opcode = "rol"
	    then
	      printOperand 0 op1
	    else
	      printOperand size op1
          val operand2 = printOperand size op2
        in
          if operand1 = "" andalso operand2 = "" then
            "        \"" ^ sizedOpcode ^ "\\n\\t\"\n"
          else if operand2 = "" then
            "        \"" ^ sizedOpcode ^ "  " ^ operand1 ^
	    "\\n\\t\"\n"
          else
            "        \"" ^ sizedOpcode ^ "  " ^ operand1 ^
	    ", " ^ operand2 ^ "\\n\\t\"\n"
        end

  fun signedToString n = (if n<0 then "-" else "") ^ Int.toString (Int.abs n)

  val regCounter = ref 15

  fun newRegister () =
    (regCounter := !regCounter + 1;
     !regCounter)

  fun setUnion [] = Splayset.empty Int.compare
    | setUnion [s] = s
    | setUnion (s :: ss) = Splayset.union (setUnion ss, s)

  val emptyset = Splayset.empty Int.compare

  fun setMinus xs ys = Splayset.difference (xs, ys)
  (* List.filter (fn x => not (List.exists (fn y => x=y) ys)) xs *)
    
  fun list2set ll = Splayset.addList (Splayset.empty Int.compare, ll)

  fun pairOrder ((x1,y1), (x2,y2)) =
    if x1 < x2 orelse x1 = x2 andalso y1 < y2 then LESS
    else if x1 = x2 andalso y1 = y2 then EQUAL
    else GREATER

  fun setUnion2 [] = Splayset.empty pairOrder
    | setUnion2 [s] = s
    | setUnion2 (s :: ss) =
       Splayset.union (setUnion2 ss, s)

  fun list2set2 ll = Splayset.addList (Splayset.empty pairOrder, ll)

  (* registers that are read even if this is a destination operand *)
  fun readRegs operand =
    case operand of
      Register r => []
    | Constant c => []
    | Indirect r => [r]
    | Offset (r, c) => [r]
    | ROffset (r1, r2) => [r1, r2]
    | Scaled (r1, r2, c) => [r1, r2]
    | NoOperand => []

  (* registers that are written if this is a destination operand
     and read only if it is a source operand *)
  fun writeRegs operand =
    case operand of
      Register r => [r]
    | _ => []

  (* registers read by instruction *)
  fun generateLiveness instr =
    case instr of
      ("cmp", z, source1, source2) =>
         list2set (writeRegs source1 @ readRegs source1 @
	           writeRegs source2 @ readRegs source2)
    | (opc, z, sourceDest, NoOperand) =>
         if String.isPrefix "set" opc
	 then list2set (readRegs sourceDest)
	 else list2set (writeRegs sourceDest @ readRegs sourceDest)
    | (opc, z, source, dest) =>
         if opc = "xor" andalso source = dest
	 then emptyset (* resets register, so dead before *)
	 else if String.isPrefix "mov" opc
	 then  list2set (writeRegs source @ readRegs source @ readRegs dest)
         else list2set (writeRegs source @ readRegs source @
	                writeRegs dest @ readRegs dest)

  (* registers written by instruction *)
  fun killLiveness instr =
    case instr of
      ("cmp", z, source1, source2) => emptyset
    | (opc, z, sourceDest, NoOperand) => list2set (writeRegs sourceDest)
    | (_, z, source, dest) => list2set (writeRegs dest)

  (* registers live at exit from instructions *)
  fun liveness instrs gen kill =
    let val (live1, _, _) = liveness1 instrs gen kill
    in
      live1
    end 

  (* one-pass liveness as there are no loops *)
  and liveness1 instrs gen kill =
    case (instrs, gen, kill) of
      ((opc, _, _, _) :: is, g :: gs, k :: ks) =>
        let
	  val (live1, liveOut, labels) = liveness1 is gs ks
	  val liveIn =
	    if String.isPrefix "jmp" opc (* unconditional jump *)
	    then labels (String.extract (opc, 4, NONE))
	    else if String.isPrefix "je" opc (* jump equal *)
	    then setUnion [liveOut, labels (String.extract (opc, 3, NONE))]
	    else if String.isPrefix "j" opc (* other conditional jump *)
	    then setUnion [liveOut, labels (String.extract (opc, 4, NONE))]
	    else setUnion [setMinus liveOut k, g]
	  val labels1 = (* update label mapping *)
	    case String.fields (fn c => c = #":") opc of
	      [l1, ""] => (fn l => if l=l1 then liveIn else labels l)
	    | _ => labels
	in
	  (liveOut :: live1, liveIn, labels1)
	end
    | _ => ([],
            emptyset,
	    (fn l => raise Error ("label " ^ l ^ " not found\n")))

  (* finds pairs of interfering registers *)
  fun interfere instrs live kill =
    case (instrs, live, kill) of
      ((opc, _, Register y, Register x) :: ins, lOut :: ls, k :: ks) =>
        setUnion2
	  [interfere ins ls ks,
	   (if String.isPrefix "mov" opc
            then list2set2
	           (List.concat
		     (List.map
		       (fn z => [(x,z), (z,x)])
		       (Splayset.listItems (setMinus lOut (list2set [x,y])))))
            else list2set2
	           (List.concat
		     (List.map
		       (fn z => [(x,z), (z,x)])
		       (Splayset.listItems (setMinus lOut (list2set [x]))))))]
    | ((opc, _, _, _) :: ins, lOut :: ls, k :: ks) =>
        setUnion2
	  [interfere ins ls ks,
	   list2set2
	     (List.concat
	       (List.map
	          (fn x =>
		    List.concat
		      (List.map
		         (fn y => [(x,y), (y,x)])
	                 (Splayset.listItems (setMinus lOut (list2set [x])))))
	          (Splayset.listItems k)))]
    | _ => list2set2 []

  (* finds register-to-register moves *)
  fun getMoves instr =
    case instr of
      (opc, _, Register x, Register y) =>
        if String.isPrefix "mov" opc
	then list2set2 [(x,y), (y,x)]
	else list2set2 []
    | _ => list2set2 []

  val spilled = ref [] (* list of spilled variables *)

  (* registers that can be allocated -- not RSP and RBP *)
  val allocatable = list2set [0,1,2,3,  5,6,  8,9,10,11,12,13,14,15]

  (* select step of graph colouring *)
  fun select [] moves mapping = mapping
    | select ((x,ys) :: stack) moves mapping =
        let
	  val ys1 = list2set (List.map mapping ys)
	  val freeRegs =
	        Splayset.listItems (setMinus allocatable ys1)
	  val moveRelated =
	        List.filter
		  (fn y => List.exists (fn (x1,y1) => (x1,mapping y1) = (x,y))
		                       moves)
		  freeRegs
	  val selected =
	    case (moveRelated, freeRegs) of
	      (y :: ys, _) => y
	    | ([], y :: ys) => y
	    | ([], []) => (spilled := x :: !spilled; x)
	in
	  select stack moves (fn y => if x=y then selected else mapping y)
	end

  (* find node with fewest neighbours *)
  fun fewestNeighbours [] (x,ys) = (x,ys)
    | fewestNeighbours ((x1,ys1) :: neighbours) (x,ys) =
        if List.length ys1 < List.length ys
	then fewestNeighbours neighbours (x1,ys1)
	else fewestNeighbours neighbours (x,ys)

  (* find best spill candidate *)
  fun bestSpill [] uses (x,ys,score) = (x,ys)
    | bestSpill ((x1,ys1) :: neighbours) uses (x,ys,score) =
         let
	   val usesOfx = Splaymap.find (uses,x)
	   val score1 = (10000 * List.length ys1) div (usesOfx + 1)
	                (* many neighbours and few uses is better *)
	 in
	   if score1 > score
	   then bestSpill neighbours uses (x1,ys1,score1)
	   else bestSpill neighbours uses (x,ys,score)
	 end

  (* remove node from graph *)
  fun remove x [] = []
    | remove x ((x1,ys) :: neighbours) =
         if x=x1 then remove x neighbours
	 else (x1, List.filter (fn y => y<>x) ys) :: remove x neighbours

  fun list2str [] = ""
    | list2str [x] = Int.toString x
    | list2str (x :: ys) = Int.toString x ^", " ^ list2str ys
  
  (* simplify step of graph colouring *)
  fun simplify [] stack moves uses = select stack moves (fn x => x)
    | simplify ((x,ys) :: neighbours) stack moves uses =
        let
	  val (x1, ys1) = fewestNeighbours neighbours (x,ys)
	  val (x2, ys2) =
	    if List.length ys1 < 14 then (x1, ys1) (* colourable *)
	    else (* find spill candidate *)
	      bestSpill ((x,ys) :: neighbours) uses (x,ys,~1)
	  val neighbours1 = remove x2 ((x,ys) :: neighbours)
	  in
            simplify neighbours1 ((x2,ys2) :: stack) moves uses
	end

  fun extractX x [] = ([], [])
    | extractX x ((x1,y1) :: pairs) =
        if x<>x1 then ([], (x1,y1) :: pairs)
	else
	  let
	    val (ys, pairs2) = extractX x pairs
	  in
	    (y1::ys, pairs2)
	  end

  fun pairs2map [] = []
    | pairs2map ((x,y)::pairs) =
        let
	  val (ys, pairs2) = extractX x pairs
	in
	  (x,y::ys) :: pairs2map pairs2
	end
	
  (* colour graph, giving a mapping of pseudoRegs to regs *)
  (* prefer register to which a pseudoReg is move-related *)
  fun colourGraph interference moves uses =
    let
      val interferesWith =
            List.filter (fn (x,ys) => x>15) (pairs2map interference)
    in
      simplify interferesWith [] moves uses
    end


  (* map pseudo registers to new registers *)
  fun reColour mapping (opc, z, op1, op2) =
    (opc, z, reColourOp mapping op1,  reColourOp mapping op2)

  and reColourOp mapping oper =
    case oper of
      Register x => Register (mapping x)
    | Constant c => Constant c
    | Indirect x => Indirect (mapping x)
    | Offset (x, c) => Offset (mapping x, c)
    | ROffset (x, y) => ROffset (mapping x, mapping y)
    | Scaled  (x, y, c) => Scaled (mapping x, mapping y, c)
    | NoOperand => NoOperand

  fun notSelfMove ("mov", _, Register x, Register y) = x<>y
    | notSelfMove _ = true

  fun leP (x,y) (x1,y1) = x1<x orelse x=x1 andalso y1<y
  fun geP x y = not (leP x y)
  
  fun sort [] = []
    | sort [x] = [x]
    | sort (x :: xs) =
        sort (List.filter (leP x) xs) @ [x] @ sort (List.filter (geP x) xs)
  
  fun printGraph interference =
    List.app
      (fn (x,y) => TextIO.output
                 (TextIO.stdErr,
                  Int.toString x ^"/"^ Int.toString y ^"\n"))
     interference

  fun printMapping mapping =
    List.app
      (fn i => if i <> mapping i then
                 TextIO.output
                   (TextIO.stdErr,
                    Int.toString i ^","^ Int.toString (mapping i) ^"\n")
	       else ())
      (List.tabulate (5000, fn i => i))

  val spillOffset = ref (~110)

  fun replaceRegOp x x1 ope =
    case ope of
      Register y => if x=y then Register x1 else ope
    | Constant c => ope
    | Indirect y => if x=y then Indirect x1 else ope
    | Offset (y,c) => if x=y then Offset (x1,c) else ope
    | ROffset (y,z) =>
        ROffset (if x=y then x1 else y, if x=z then x1 else z)
    | Scaled (y,z,c) =>
        Scaled (if x=y then x1 else y, if x=z then x1 else z, c)
    | NoOperand => ope

  fun replaceReg x x1 (opc, z, op1, op2) =
    (opc, z, replaceRegOp x x1 op1, replaceRegOp x x1 op2)

  fun spill x offset [] = []
    | spill x offset (instr :: instrs) =
         let
	   val reads = generateLiveness instr
	   val writes = killLiveness instr
	   val instrs1 = spill x offset instrs
	   val x1 = newRegister ()
	 in
	   case (Splayset.member (reads, x), Splayset.member (writes, x)) of
	     (false, false) => instr :: instrs1
	   | (true, false) =>
	       ("mov", 3, Offset (rbp, offset), Register x1)
	       :: (replaceReg x x1 instr)
	       :: instrs1
	   | (false, true) =>
	       (replaceReg x x1 instr)
	       :: ("mov", 3, Register x1, Offset (rbp, offset))
	       :: instrs1
	   | (true, true) =>
	       ("mov", 3, Offset (rbp, offset), Register x1)
	       :: (replaceReg x x1 instr)
	       :: ("mov", 3, Register x1, Offset (rbp, offset))
	       :: instrs1
	 end

  fun spillList [] instrs = instrs
    | spillList (x :: xs) instrs =
        let
          val _ = TextIO.output
	             (TextIO.stdErr, "spill register " ^ Int.toString x ^ "\n")
	  val offset =
	    signedToString (spillOffset := !spillOffset - 8; !spillOffset)
	  val instrs1 = spill x offset instrs
	in
	  spillList xs instrs1
	end

  
  fun findUses [] = Splaymap.mkDict Int.compare
    | findUses (ins :: instrs) =
        let
	  val uses = findUses instrs
	  val regs = Splayset.listItems
	               (setUnion [generateLiveness ins, killLiveness ins])
	in
          List.foldl
	    (fn (r, u) => case Splaymap.peek (u, r) of
	                    NONE => Splaymap.insert (u,r,1)
	                  | SOME c => Splaymap.insert (u,r,c+1))
            uses regs
	end

  fun registerAllocate instrs =
    let
      val _ = spilled := []
      val uses = findUses instrs
      val gen = List.map generateLiveness instrs
      val kill = List.map killLiveness instrs
      val live = liveness instrs gen kill
      val interference0 = interfere instrs live kill
      val interference = Splayset.listItems interference0
      val moves = Splayset.listItems (setUnion2 (List.map getMoves instrs))
      val mapping = colourGraph interference moves uses
    in
      if null (!spilled) then
        let
          val newInstrs = List.map (reColour mapping) instrs
          val withoutSelf = List.filter notSelfMove newInstrs
        in
          (withoutSelf, !spillOffset - 16)
        end
      else
        registerAllocate (spillList (!spilled) instrs)
    end
end