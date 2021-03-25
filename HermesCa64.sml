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
      val maskDown =
        case size of
            Hermes.U8 => [(a64.AND, src, src, a64.Imm(0xff))]
          | Hermes.U16 => [(a64.AND, src, src, a64.Imm(0xffff))]
          | Hermes.U32 => [(a64.AND, src, src, a64.Imm(0xffffffff))]
          | Hermes.U64 => []
      fun extend Hermes.U8 =
          [(a64.LSL, a64.Register r1, src, a64.Imm(8)),
          (a64.ORR, src, src, a64.Register r1)] @
          extend Hermes.U16
        | extend Hermes.U16 =
          [(a64.LSL, a64.Register r1, src, a64.Imm(16)),
          (a64.ORR, src, src, a64.Register r1)] @
          extend Hermes.U32
        | extend Hermes.U32 =
          [(a64.LSL, a64.Register r1, src, a64.Imm(32)),
          (a64.ORR, src, src, a64.Register r1)] @
          extend Hermes.U64
        | extend Hermes.U64 = [] (*to silence compiler*)
    in
      (extend size, maskDown)
    end

  (* Debugging functions *)
  fun debugStat Hermes.Skip                 = "Skip"
    | debugStat (Hermes.Update(_,_,_,_))    = "Update"
    | debugStat (Hermes.Swap(_,_,_))        = "Swap"
    | debugStat (Hermes.CondSwap(_,_,_,_))  = "CondSwap"
    | debugStat (Hermes.If(_,_,_,_))        = "If"
    | debugStat (Hermes.For(_,_,_,_,_))     = "For"
    | debugStat (Hermes.Call(_,_,_))        = "Call"
    | debugStat (Hermes.Uncall(_,_,_))      = "Uncall"
    | debugStat (Hermes.Block(_,_,_))       = "Block"
    | debugStat (Hermes.Assert(_,_))        = "Assert" 


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
          (Hermes.Var (s, p)) =>
            let
              val (t, vReg) = lookup s env p
            in
              [(a64.MOV, target, vReg, a64.NoOperand)]
            end
          (* | (Hermes.Array (s, e, p)) =>
            let
              
            in
            
            end *)
      | _ => [(a64.LABEL ("compilExp:" ^ Hermes.showExp exp true), 
              a64.NoOperand, a64.NoOperand, a64.NoOperand)]

        
  

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
              val (setup, maskDown) = 
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
              eCode @ setup @ [(opc, vReg, vReg, (a64.Register eReg))] @ maskDown
            end
          | Hermes.Array(s, i, p) =>
            (*
              1. compile i
              2. load whatever iReg holds
              3. Do the update
              4. Write value back to array index location
            *)
            let
              val (t, vReg) = lookup s env p
              val iReg = a64.newRegister ()
              val iCode = compileExp i (a64.Register iReg) env p
              val tmp = a64.newRegister ()
              val mulReg = a64.newRegister ()
              (* find ldr and store sizes *)
              val (ldr, str, reg, off) =
                case t of
                  Hermes.U8    => (a64.LDRB, a64.STRB, a64.RegisterW, 1)
                  | Hermes.U16 => (a64.LDRH, a64.STRH, a64.RegisterW, 2)
                  | Hermes.U32 => (a64.LDRW, a64.STRW, a64.RegisterW, 4)
                  | Hermes.U64 => (a64.LDR,  a64.STR,  a64.Register,  8)
              val load = 
                [(a64.MOV, a64.Register mulReg, a64.Imm off, a64.NoOperand),
                (a64.MUL, a64.Register iReg, a64.Register iReg, a64.Register mulReg),
                (ldr, reg tmp, a64.BaseOffset(vReg, a64.Register iReg), a64.NoOperand)]
              val save = [(str, reg tmp, a64.BaseOffset(vReg, a64.Register iReg), a64.NoOperand)]
              val (setup, maskDown) = 
                case uop of
                Hermes.RoR => extendBits vReg t
                | Hermes.RoL =>
                  let
                    val (set, clean) = extendBits vReg t
                    val rev = [(a64.RBIT, vReg, vReg, a64.NoOperand)]
                  in 
                    (set @ rev, rev @ clean)
                  end
                | _ => ([], [])
            in
              (* overwrites vReg since all calculations are redone each statement *)
              eCode @ iCode @ load @ setup @ [(opc, vReg, vReg, (a64.Register tmp))] @ maskDown @ save
            end
          | Hermes.UnsafeArray(s, i, p) =>
              compileStat (Hermes.Update (uop, Hermes.Array (s, i, p), e, pos)) env       
        end
      | _ => [(a64.LABEL ("compilStat: " ^ debugStat stat), 
              a64.NoOperand, a64.NoOperand, a64.NoOperand)]
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
      
      val bodyCode = compileStat body env
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
            prologue1 @ saveCallee  @ bodyCode  @
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