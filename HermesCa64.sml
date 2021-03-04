(* Assembler *)

structure HermesCa64 = 
struct

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