(* Assembler *)

structure HermesCa64 = 
struct

  fun translateUop Hermes.Add = a64.ADD
    | translateUop Hermes.Sub = a64.SUB
    | translateUop Hermes.RoL = a64.ROR (*Take care!!!*)
    | translateUop Hermes.Ror = a64.ROR
    | translateUop Hermes.XorWith = a64.EOR

    (* lookup in environment *)
  fun lookup x [] pos =
        raise Error ("undeclared identifier: " ^ x, pos)
    | lookup x ((y,v) :: env) pos =
        if x = y then v else lookup x env pos


  fun compileExp exp target env pos =
    case exp of
      Hermes.Const(n, _) =>
        (* LDR Rn, =0x87654321 *)
        [(a64.LDR, target, a64.Literal(n), a64.NoOperand)]
  
  (* Create sequence of instructions to duplicate values to all bytes *)
  fun extendBits src size =
    let 
      val r1 = a64.newRegister ()
    in
    case size of
      Hermes.U8 => (* change this to 64 bit instead of 32? *)
        ([
          (a64.LSL, a64.Register(r1, 0), src, a64.Imm(8)),
          (a64.ORR, a64.Register(r1, 0), a64.Register(r1, 0), src),
          (a64.LSL, src, a64.Register(r1, 0), a64.Imm(16)),
          (a64.ORR, src, src, a64.Register(r1, 0))
        ],
        [
          (a64.AND, src, src, a64.Imm(0xff))
        ])
      | Hermes.U16 =>
        ([
          (a64.MOV, a64.Register(r1, 0), src, a64.NoOperand) 
          (a64.LSL, src, src, a64.Imm(16)),
          (a64.ORR, src, src, a64.Register(r1, 0))
        ],
        [
          (a64.AND, src, src, a64.Imm(0xffff))
        ])
      | _ => ([], [])
    end
          


  fun compileStat stat env =
    (case stat of
      Hermes.Skip => []
      (* | Hermes.Update (uop, Hermes.Var (name1, p1), Hermes.Const (name2, p2), pos) => *)
      | Hermes.Update (uop, lval, e, pos) =>
        let
          val opc = translateUop uop
          val eReg = newRegister ()
          val eCode = compileExp e (a64.Register eReg, 1) env pos
        in
        case lval of
          Hermes.Var(n, p) =>
            let 
              val (t, vReg) = lookup n env p
              val size = HermesCx64.hSize t
              val (setup, cleanup) = 
                case uop of
                  Hermes.RoR => extendBits vReg size
                  Hermes.RoL => 
                    let
                      (*RBIT => Rotate bits then right shif tthen rotate again*)
                    in
                    end
                  | _ => ([], [])

            in
              eCode @ setup @ [(opc, vReg, vReg, (a64.Register eReg, 1)] @ cleanup
            end

        end



     
     
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




  )

  fun compileA64Args [] locs = ([], [], [])
      | compileA64Args _ [] =
          raise Error ("Not enough parameter locations", (0,0))
      | compileA64Args (Hermes.VarArg (x, (_, it), _) :: args) (l1 :: locs) =
          let
            val (env, code0, code1) = compileA64Args args locs
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


  fun compileProcedure f args body =
    let
      val parameterLocations =
        List.map a64.Register a64.argRegs @
        List.map (fn n => a64.ImmOffset(rbp, signedToString n, 1))
                [16,24,32,40,48]
      val arglist = HermesCx64.compileCArgs args
      val (env, prologue1, epilogue0) = compileA64Args args parameterLocations
      val saveCallee = (* save callee-saves variables *)
            [(a64.STR, a64.Register (19, 1), a64.ImmOffset (a64.fp, "-56", 1), a64.NoOperand),
            (a64.STR, a64.Register (20, 1), a64.ImmOffset (a64.fp, "-64", 1), a64.NoOperand),
            (a64.STR, a64.Register (21, 1), a64.ImmOffset (a64.fp, "-72", 1), a64.NoOperand),
            (a64.STR, a64.Register (22, 1), a64.ImmOffset (a64.fp, "-80", 1), a64.NoOperand),
            (a64.STR, a64.Register (23, 1), a64.ImmOffset (a64.fp, "-88", 1), a64.NoOperand),
            (a64.STR, a64.Register (24, 1), a64.ImmOffset (a64.fp, "-96", 1), a64.NoOperand),
            (a64.STR, a64.Register (25, 1), a64.ImmOffset (a64.fp, "-104", 1), a64.NoOperand),
            (a64.STR, a64.Register (26, 1), a64.ImmOffset (a64.fp, "-112", 1), a64.NoOperand),
            (a64.STR, a64.Register (27, 1), a64.ImmOffset (a64.fp, "-120", 1), a64.NoOperand),
            (a64.STR, a64.Register (28, 1), a64.ImmOffset (a64.fp, "-128", 1), a64.NoOperand),
            (a64.STR, a64.SP, a64.ImmOffset (a64.fp, "-136", 1), a64.NoOperand), (* save SP on stack*)
            (a64.STR, a64.Register (31, 1), a64.ImmOffset (a64.fp, "-144", 1), a64.NoOperand) (* error code *)
            (a64.STR, a64.Register (a64.SP, a64.ImmOffset(a64.fp, "-999", 1)))] (*placeholder, LEA in x86*)
      
      val bodyCode = compileStat body env
      val epilogue1 =
            [(a64.Label ("exit_label_:"), a64.NoOperand, a64.NoOperand, a64.NoOperand),
            (a64.LDR, a64.Register (0, 1), a64.ImmOffset (a64.fp, "-136"), a64.NoOperand)]
      val restoreCallee = (* restore callee-saves variables *)
            [(a64.LDR, a64.Register (19, 1), a64.ImmOffset (a64.fp, "-56", 1), a64.NoOperand),
            (a64.LDR, a64.Register (20, 1), a64.ImmOffset (a64.fp, "-64", 1), a64.NoOperand),
            (a64.LDR, a64.Register (21, 1), a64.ImmOffset (a64.fp, "-72", 1), a64.NoOperand),
            (a64.LDR, a64.Register (22, 1), a64.ImmOffset (a64.fp, "-80", 1), a64.NoOperand),
            (a64.LDR, a64.Register (23, 1), a64.ImmOffset (a64.fp, "-88", 1), a64.NoOperand),
            (a64.LDR, a64.Register (24, 1), a64.ImmOffset (a64.fp, "-96", 1), a64.NoOperand),
            (a64.LDR, a64.Register (25, 1), a64.ImmOffset (a64.fp, "-104", 1), a64.NoOperand),
            (a64.LDR, a64.Register (26, 1), a64.ImmOffset (a64.fp, "-112", 1), a64.NoOperand),
            (a64.LDR, a64.Register (27, 1), a64.ImmOffset (a64.fp, "-120", 1), a64.NoOperand),
            (a64.LDR, a64.Register (28, 1), a64.ImmOffset (a64.fp, "-128", 1), a64.NoOperand),
            (a64.LDR, a64.SP, a64.ImmOffset (a64.fp, "-136", 1), a64.NoOperand)]
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


end