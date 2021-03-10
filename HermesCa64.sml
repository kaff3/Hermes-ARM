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



fun compileProcedure f args body =
  let
    val parameterLocations =
      List.map a64.Register a64.argRegs @
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