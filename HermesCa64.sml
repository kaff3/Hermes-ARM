(* Assembler *)

structure HermesCa64 = 
struct

(* TODO: strings eller a64.ADD osv? *)
fun translateUop Hermes.Add = "ADD"
  | translateUop Hermes.Sub = "SUB"
  | translateUop Hermes.RoL = "ROR" (*Take care!!!*)
  | translateUop Hermes.Ror = "ROR"
  | translateUop Hermes.XorWith = "EOR"


(* Used for creation of pseudo registers *)
val regCounter = ref 32
fun newRegister () =
  (regCounter := !regCounter + 1; !regCounter)



(* fun evalLval lval env pos : (int, string) =
  case lval of
    Hermes.Var(x, p1) =>
      val (t1, loc) HermesCx64.lookup x env
      val size = HermesCx64.hSize t1
      val bits = 8 * HermesCx64.size2bytes size
      val opc  = translateUop uop 
      (size, opc) *)

(* parameters: args, locations *)
fun compileA64Args [] 

fun compileExp exp target env pos =
  case exp of
    Hermes.Const(n, _) =>
      (* LDR Rn, =0x87654321 *)
      [(a64.LDR, target, a64.Literal(n), a64.NoOperand)]
      

fun compileStat stat env =
  (case stat of
    Hermes.Skip => []
    (* | Hermes.Update (uop, Hermes.Var (name1, p1), Hermes.Const (name2, p2), pos) => *)
    | Hermes.Update (uop, lval, e, pos) =>
      let
        val opc = translateUop uop
        val eReg = newRegister ()
        val eCode = compileExp e (a64.Register eReg) env pos
      in
      case lval of
        Hermes.Var(n, p) =>


     
     
      (* let
        val opcode = translateUop uop
      in
      case (lval, e) of
        (Hermes.Var (n1, p1), Hermes.Const (n2, p2)) =>
          let 
            val (t, loc) = HermesCx64.lookup x env p1
            val size = HermesCx64.hSize t
            val bits = 8 * HermesCx64.size2bytes size
            val hNum = BigInt.string2h n2 pos
            val hNumSized = BigInt.limitZ bits hNum
            val n2New = BigInt.h2hstring hNumSized
            val maxImm = BigInt *)



      (* let
        val opcode = translateUop uop
        val (size, )
      case lval of 
        Hermes.Var(name, p) => 
          let 
            val (t, loc) = HermesCx64.lookup x env p
            val size = HermesCx64.hSize t
            val bits = 8 * HermesCx64.size2bytes size
            val opcode = translateUop uop
            val hNum = BigInt.string2h  *)



      (* let
        val (size, _lval) = evalLval lval env pos

      val _uop = 
        case uop of
          Hermes.Add =>
            [(, )] *)




  )

fun compileA64Args [] locs = ([], [], [])
    | compileA64Args _ [] = 
        raise Error ("Not enough parameter locations", (0,0))
    | compileA64Args (Hermes.VarArg (x, (_, it), _) :: args) (l1 :: locs) = 
        let
          val (env, code0, code1) = compileA64Args args locs
          val r = newRegister (); val r1 = newRegister ()
          in
            ((x,(it,x86.Register r)))


fun compileProcedure f args body =
  let
    val parameterLocations =
      List.map a64.Register a64.argRegs @
      List.map (fn n => x86.Offset(rbp, signedToString n))
               [16,24,32,40,48]
    val arglist = compileCArgs args
    val (env, prologue1, epilogue0) = compileA64Args args parameterLocations
    val saveCallee = (* save callee-saves variables *)
          [(a64.STR, a64.Register (19, 1), a64.ImmOffset (a64.fp, "-56"), a64.NoOperand),
          (a64.STR, a64.Register (20, 1), a64.ImmOffset (a64.fp, "-64"), a64.NoOperand),
          (a64.STR, a64.Register (21, 1), a64.ImmOffset (a64.fp, "-72"), a64.NoOperand),
          (a64.STR, a64.Register (22, 1), a64.ImmOffset (a64.fp, "-80"), a64.NoOperand),
          (a64.STR, a64.Register (23, 1), a64.ImmOffset (a64.fp, "-88"), a64.NoOperand),
          (a64.STR, a64.Register (24, 1), a64.ImmOffset (a64.fp, "-96"), a64.NoOperand),
          (a64.STR, a64.Register (25, 1), a64.ImmOffset (a64.fp, "-104"), a64.NoOperand),
          (a64.STR, a64.Register (26, 1), a64.ImmOffset (a64.fp, "-112"), a64.NoOperand),
          (a64.STR, a64.Register (27, 1), a64.ImmOffset (a64.fp, "-120"), a64.NoOperand),
          (a64.STR, a64.Register (28, 1), a64.ImmOffset (a64.fp, "-128"), a64.NoOperand),
          (a64.STR, a64.Register (31, 1), a64.ImmOffset (a64.fp, "-136"), a64.NoOperand) (* error code *)
          (* move stackpointer *)
          (* spilled variables *) 
          ]
    
    val bodyCode = compileStat body env
    val epilogue1 =
          [(a64.Label ("exit_label_:"), a64.NoOperand, a64.NoOperand, a64.NoOperand),
	        (a64.LDR, a64.Register (0, 1), a64.ImmOffset (a64.fp, "-136"), a64.NoOperand)]
    val restoreCallee = (* restore callee-saves variables *)
          [(a64.LDR, a64.Register (19, 1), a64.ImmOffset (a64.fp, "-56"), a64.NoOperand),
          (a64.LDR, a64.Register (20, 1), a64.ImmOffset (a64.fp, "-64"), a64.NoOperand),
          (a64.LDR, a64.Register (21, 1), a64.ImmOffset (a64.fp, "-72"), a64.NoOperand),
          (a64.LDR, a64.Register (22, 1), a64.ImmOffset (a64.fp, "-80"), a64.NoOperand),
          (a64.LDR, a64.Register (23, 1), a64.ImmOffset (a64.fp, "-88"), a64.NoOperand),
          (a64.LDR, a64.Register (24, 1), a64.ImmOffset (a64.fp, "-96"), a64.NoOperand),
          (a64.LDR, a64.Register (25, 1), a64.ImmOffset (a64.fp, "-104"), a64.NoOperand),
          (a64.LDR, a64.Register (26, 1), a64.ImmOffset (a64.fp, "-112"), a64.NoOperand),
          (a64.LDR, a64.Register (27, 1), a64.ImmOffset (a64.fp, "-120"), a64.NoOperand),
          (a64.LDR, a64.Register (28, 1), a64.ImmOffset (a64.fp, "-128"), a64.NoOperand),
          (a64.LDR, a64.Register (31, 1), a64.ImmOffset (a64.fp, "-136"), a64.NoOperand)
          ]
        val epilogue3 = [("xor", 3, x86.Register 10, x86.Register 10),
    		     ("xor", 3, x86.Register 11, x86.Register 11)] (* Zero caller-saves registers not used for parameters *)
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