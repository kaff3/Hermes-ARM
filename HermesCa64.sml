(* Assembler *)

structure HermesCa64 = 
struct

  (*
      Functions for translanting between Hermes and arm instructions
  *)
  fun translateUop Hermes.Add = a64.ADD
    | translateUop Hermes.Sub = a64.SUB
    | translateUop Hermes.RoL = a64.ROR (*Take care!!!*)
    | translateUop Hermes.RoR = a64.ROR
    | translateUop Hermes.XorWith = a64.EOR

  (*
      Helper Functions
  *)
  (* Create sequence of instructions to duplicate values to all bytes *)
  fun extendBits src size =
    let 
      val r1 = a64.newRegister ()
    in
    case size of
      Hermes.U8 => (* change this to 64 bit instead of 32? *)
        ([
          (a64.LSL, a64.Register r1, src, a64.Imm(8)),
          (a64.ORR, a64.Register r1, a64.Register r1, src),
          (a64.LSL, src, a64.Register r1, a64.Imm(16)),
          (a64.ORR, src, src, a64.Register r1)
        ],
        [
          (a64.AND, src, src, a64.Imm(0xff))
        ])
      | Hermes.U16 =>
        ([
          (a64.MOV, a64.Register r1, src, a64.NoOperand),
          (a64.LSL, src, src, a64.Imm(16)),
          (a64.ORR, src, src, a64.Register r1)
        ],
        [
          (a64.AND, src, src, a64.Imm(0xffff))
        ])
      | _ => ([], [])
    end


  (*
      Functions used for compiling
  *)

  (* fun declareArgs [] = "\n"
  | declareArgs (Hermes.VarArg (x, (_, it), _) :: args) =
      "  " ^ cType it ^ "arg_" ^ x ^ ";\n" ^ declareArgs args
  | declareArgs (Hermes.ArrayArg (x, (_, it), _) :: args) =
      "  " ^  cType it ^ "*arg_" ^ x ^ ";\n" ^ declareArgs args *)

  (* lookup in environment *)
  fun lookup x [] pos =
        raise HermesCx64.Error ("undeclared identifier: " ^ x, pos)
    | lookup x ((y,v) :: env) pos =
        if x = y then v else lookup x env pos


  fun compileExp exp target env pos =
    case exp of
      Hermes.Const(n, _) =>
        (* LDR Rn, =0x87654321 *)
        [(a64.LDR, target, a64.Literal(n), a64.NoOperand)]
      | (Hermes.Rval lval )=>
        case lval of
          (Hermes.Var (s, p)) => (*TODO: godkendelse*)
            let
              val (t, vReg) = lookup s env p
            in
              [(a64.MOV, target, vReg, a64.NoOperand)]
            end
          (* | (Hermes.Array (s, e, p)) =>
            let
              
            in
            
            end *)

        
  

  fun compileStat stat env =
    (case stat of
      Hermes.Skip => []
      | Hermes.Update (uop, lval, e, pos) =>
        let
          val opc = translateUop uop
          val eReg = a64.newRegister ()
          val eCode = compileExp e (a64.Register eReg) env pos
        in
        case lval of
          Hermes.Var(n, p) =>
            let 
              val (t, vReg) = lookup n env p
              (* val size = HermesCx64.hSize t *)
              val (setup, cleanup) = 
                case uop of
                  Hermes.RoR => extendBits vReg t
                  | Hermes.RoL => 
                    let
                      (* Reverse, right rotate, reverse *)
                      val (set, clean) = extendBits vReg t
                      val rev = [(a64.RBIT, vReg, vReg, a64.NoOperand)]
                    in
                      (set @ rev, rev @ clean)
                    end
                  | _ => ([], [])
            in
              eCode @ setup @ [(opc, vReg, vReg, (a64.Register eReg))] @ cleanup
            end
          (* | Hermes.Array(s, e, p) =>
            let
              val (t, vReg) = lookup s env p
              val eReg = a64.newRegister ()
              val eCode = compileExp (a64.Register eReg) env p
            in
              
            end *)
        end
    )

  fun compileA64Args [] locs = ([], [], [])
      | compileA64Args _ [] =
          raise HermesCx64.Error ("Not enough parameter locations", (0,0))
      | compileA64Args (Hermes.VarArg (x, (_, it), _) :: args) (l1 :: locs) =
          let
            val (env, code0, code1) = compileA64Args args locs
            val r = a64.newRegister ()
            val r1 = a64.newRegister ()
          in
            (* call by value result *)
            ((x, (it, a64.Register r)) :: env,
            [(a64.MOV, a64.Register r1, l1, a64.NoOperand),
            (a64.LDR, a64.Register r, a64.RegAddr r1, a64.NoOperand)]
            @ code0,
            code1 @
            [(a64.STR, a64.Register r, a64.RegAddr r1, a64.NoOperand),
            (a64.MOV, l1, a64.Register r1, a64.NoOperand)])
          end
      | compileA64Args (Hermes.ArrayArg (x, (_, it), _) :: args) (l1 :: locs) =
          let
            val (env, code0, code1) = compileA64Args args locs
            val r = a64.newRegister ()
          in
            ((x,(it,a64.Register r)) :: env,
            [(a64.MOV, a64.Register r, l1, a64.NoOperand)]
            @ code0,
            code1 @
            [(a64.MOV, l1, a64.Register r, a64.NoOperand)])
          end


  fun compileProcedure f args body =
    let
      val parameterLocations =
        List.map a64.Register a64.argRegs @
        List.map (fn n => a64.ImmOffset(a64.fp, HermesCx64.signedToString n))
                [16,24,32,40,48]
      val arglist = HermesCx64.compileCArgs args
      val (env, prologue1, epilogue0) = compileA64Args args parameterLocations
      val saveCallee = (* save callee-saves variables *)
            [(a64.STR, a64.Register 19, a64.ImmOffset (a64.fp, "-56"), a64.NoOperand),
            (a64.STR, a64.Register 20, a64.ImmOffset (a64.fp, "-64"), a64.NoOperand),
            (a64.STR, a64.Register 21, a64.ImmOffset (a64.fp, "-72"), a64.NoOperand),
            (a64.STR, a64.Register 22, a64.ImmOffset (a64.fp, "-80"), a64.NoOperand),
            (a64.STR, a64.Register 23, a64.ImmOffset (a64.fp, "-88"), a64.NoOperand),
            (a64.STR, a64.Register 24, a64.ImmOffset (a64.fp, "-96"), a64.NoOperand),
            (a64.STR, a64.Register 25, a64.ImmOffset (a64.fp, "-104"), a64.NoOperand),
            (a64.STR, a64.Register 26, a64.ImmOffset (a64.fp, "-112"), a64.NoOperand),
            (a64.STR, a64.Register 27, a64.ImmOffset (a64.fp, "-120"), a64.NoOperand),
            (a64.STR, a64.Register 28, a64.ImmOffset (a64.fp, "-128"), a64.NoOperand),
            (a64.STR, a64.SP, a64.ImmOffset (a64.fp, "-136"), a64.NoOperand), (* save SP on stack*)
            (a64.STR, a64.Register 31, a64.ImmOffset (a64.fp, "-144"), a64.NoOperand), (* error code *)
            (a64.STR, a64.SP, a64.ImmOffset(a64.fp, "-999"), a64.NoOperand)] (*placeholder, LEA in x86*)
      
      (* val bodyCode = compileStat body env *)
      val epilogue1 =
            [(a64.LABEL ("exit_label_:"), a64.NoOperand, a64.NoOperand, a64.NoOperand),
            (a64.LDR, a64.Register 0, a64.ImmOffset (a64.fp, "-144"), a64.NoOperand)]
      val restoreCallee = (* restore callee-saves variables *)
            [(a64.LDR, a64.Register 19, a64.ImmOffset (a64.fp, "-56"), a64.NoOperand),
            (a64.LDR, a64.Register 20, a64.ImmOffset (a64.fp, "-64"), a64.NoOperand),
            (a64.LDR, a64.Register 21, a64.ImmOffset (a64.fp, "-72"), a64.NoOperand),
            (a64.LDR, a64.Register 22, a64.ImmOffset (a64.fp, "-80"), a64.NoOperand),
            (a64.LDR, a64.Register 23, a64.ImmOffset (a64.fp, "-88"), a64.NoOperand),
            (a64.LDR, a64.Register 24, a64.ImmOffset (a64.fp, "-96"), a64.NoOperand),
            (a64.LDR, a64.Register 25, a64.ImmOffset (a64.fp, "-104"), a64.NoOperand),
            (a64.LDR, a64.Register 26, a64.ImmOffset (a64.fp, "-112"), a64.NoOperand),
            (a64.LDR, a64.Register 27, a64.ImmOffset (a64.fp, "-120"), a64.NoOperand),
            (a64.LDR, a64.Register 28, a64.ImmOffset (a64.fp, "-128"), a64.NoOperand),
            (a64.LDR, a64.SP, a64.ImmOffset (a64.fp, "-136"), a64.NoOperand)]
          (* val epilogue3 = [("xor", 3, x86.Register 10, x86.Register 10),
              ("xor", 3, x86.Register 11, x86.Register 11)] Zero caller-saves registers not used for parameters *)
      val allCode =
            prologue1 @ saveCallee (* @ bodyCode *) @
      epilogue0 @ epilogue1 @ restoreCallee (*@ epilogue3*)
      (* val (newCode, offset) = x86.registerAllocate allCode *)
      (* val newCode1 = replace999 newCode (signedToString offset) *)
    in
      "int " ^ f ^ "(" ^ arglist ^ ")\n" ^
      "{\n  asm volatile ( \n" ^
      String.concat (List.map a64.printInstruction allCode) ^
      "  );\n}\n\n"
    end 


end