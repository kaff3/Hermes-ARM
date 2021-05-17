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
  
  fun translateBop Hermes.Plus  pos = a64.ADD
    | translateBop Hermes.Minus pos = a64.SUB
    | translateBop Hermes.Times pos = a64.MUL
    (* | translateBop Hermes.Divide = a64.DIV *)
    (* | translateBop Hermes.Modulo = ????? *)
    | translateBop Hermes.Xor    pos = a64.EOR
    | translateBop Hermes.BAnd   pos = a64.AND
    | translateBop Hermes.BOr    pos = a64.ORR
    | translateBop Hermes.ShiftL pos = a64.LSL
    | translateBop Hermes.ShiftR pos = a64.LSR
    | translateBop _ pos = raise HermesCx64.Error("Binop not implemented", pos)
    

  (*----- Helper Functions -----*)

  fun decToHex dec =
    if String.isPrefix "0x" dec then
      dec
    else
      let 
        val decInt = Option.getOpt (Int.fromString dec, 9999)
      in
        Int.fmt StringCvt.HEX decInt 
      end

  fun isComparison bop =
    List.exists (fn cmp => cmp = bop)
      [Hermes.Equal, Hermes.Less, Hermes.Greater, 
       Hermes.Neq, Hermes.Leq, Hermes.Geq]

  fun maskDown src size = 
    case size of
        Hermes.U8 => [(a64.AND, src, src, a64.Imm(0xff))]
      | Hermes.U16 => [(a64.AND, src, src, a64.Imm(0xffff))]
      | Hermes.U32 => [(a64.AND, src, src, a64.Imm(0xffffffff))]
      | Hermes.U64 => []

  fun type2Bytes t =
    case t of
        Hermes.U8 => 1
      | Hermes.U16 => 2
      | Hermes.U32 => 4
      | Hermes.U64 => 8
    
  fun string2Int s =
    Option.getOpt (Int.fromString s, 9999)
  
  fun int2String i =
    Int.toString i

    
  (* Returns the corresponding LDR, STR, Register(W) and byte size for a hermes intType *)
  fun getForType t =
    case t of 
      Hermes.U8  => (a64.LDRB, a64.STRB, a64.RegisterW, 1)
    | Hermes.U16 => (a64.LDRH, a64.STRH, a64.RegisterW, 2)
    | Hermes.U32 => (a64.LDR,  a64.STR,  a64.RegisterW, 4)
    | Hermes.U64 => (a64.LDR,  a64.STR,  a64.Register,  8)

  (* Create sequence of instructions to duplicate values to all bytes *)
  fun extendBits src size =
    let 
      val r1 = a64.newRegister ()
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
      (extend size)
    end

  (* ----- Debugging functions -----*)

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

  (* lookup in environment *)
  fun lookup x [] pos =
        raise HermesCx64.Error ("undeclared identifier: " ^ x, pos)
    | lookup x ((y,v) :: env) pos =
        if x = y then v else lookup x env pos


  fun compileExp exp target env pos =
    case exp of
      Hermes.Const(n, _) =>
        [(a64.LDR, a64.Register target, a64.PoolLit n, a64.NoOperand)]
      
      | (Hermes.Rval lval )=>
        (case lval of
          (* If Rval is a var *)
          (Hermes.Var (s, p)) =>
            let val (_, vReg) = lookup s env p in
              [(a64.MOV, a64.Register target, a64.Register vReg, a64.NoOperand)]
            end
          
          (* If Rval is array with constant index *)
          | (Hermes.Array (s, Hermes.Const(n, _), p)) =>
            let
              val (t, vReg) = lookup s env p
              val (ldr, _, reg, size) = getForType t
              val offset = size * (string2Int n)
              val (maxImm, mulOf) = 
                (case t of 
                    Hermes.U64 => (32760, 8) 
                  | Hermes.U32 => (16380, 4)
                  | _ =>
                    (case ldr of
                        a64.LDRH => (8190, 2)
                      | a64.LDRB => (4095, 1)
                      | _ => (9999, 9999) (* should never happen *)
                    )
                )
              (* TODO: Behøver måske ikke tjekke med mulOf. Skulle meget gerne altid
                 Være det? *)
              (* TODO: Potential sidechannel attack? *)
              val ldrCode =
                if offset < maxImm andalso offset mod mulOf = 0 then
                  [(ldr, reg target, a64.ABaseOffI(vReg, int2String offset), a64.NoOperand)] 
                else
                  let
                    val iReg = a64.newRegister ()
                  in
                    [(a64.LDR, a64.Register iReg, a64.PoolLit (int2String offset), a64.NoOperand),
                     (ldr, reg target, a64.ABaseOffR(vReg, iReg), a64.NoOperand)]
                  end
            in
              ldrCode
            end

          (* If Rval is an array with non-constant index *)
          | (Hermes.Array (s, e, p)) =>
            let
              val (t1, vReg) = lookup s env p
              val eReg    = a64.newRegister ()
              val sizeReg = a64.newRegister ()

              val eCode = compileExp e eReg env pos
              val (ldr, _, reg, size) = getForType t1
              val size = Int.toString size
              val loadCode = [
                (a64.LDR, a64.Register sizeReg, a64.PoolLit size, a64.NoOperand),      
                (a64.MUL, a64.Register eReg, a64.Register eReg, a64.Register sizeReg), 
                (ldr, reg target, a64.ABaseOffR(vReg, eReg), a64.NoOperand)]
            in
              eCode @ loadCode
            end

          (* If Rval is an unsafe array*)
          | Hermes.UnsafeArray(x, e, p) => 
            compileExp (Hermes.Rval (Hermes.Array(x,e,pos))) target env pos
        )

      | Hermes.Un (Hermes.Negate, e, p) =>
        let
          (*Always on 64-bit values? *)
          val eCode = compileExp e target env p
          val negCode = [(a64.MVN, a64.Register target, a64.Register target, a64.NoOperand)]
        in
          eCode @ negCode
        end
      
      (* Binary operator with right side being a constant *)
      (* | Hermes.Bin (bop, e1, Hermes.Const(n, _), p) =>
        let
          val e1Reg  = a64.newRegister ()
          val e1Code = compileExp e1 e1Reg env p
        in
        end *)

      (* Binary operator *)
      | Hermes.Bin (bop, e1, e2, p) =>
        let
          val e2Reg = a64.newRegister ()
          val e1Code = compileExp e1 target env p
          val e2Code = compileExp e2 e2Reg env p

          val bopCode = 
            if isComparison bop then
              let
                val cond =
                  (case bop of 
                      Hermes.Equal   => a64.EQ
                    | Hermes.Less    => a64.LS
                    | Hermes.Greater => a64.HI
                    | Hermes.Neq     => a64.NE
                    | Hermes.Leq     => a64.LS
                    | Hermes.Geq     => a64.HI
                    | _ => raise HermesCx64.Error ("Condition not implemented", p)
                  )
                val compCode = [
                  (a64.CMP, a64.Register target, a64.Register e2Reg, a64.NoOperand),
                  (a64.CSETM, a64.Register target, a64.Cond cond, a64.NoOperand)
                ]
                val tmpReg = a64.newRegister ()
                val handleCode =
                  if bop = Hermes.Less orelse bop = Hermes.Geq then
                      [(a64.CSETM, a64.Register tmpReg, a64.Cond a64.NE, a64.NoOperand),
                       (a64.AND, a64.Register target, a64.Register target, a64.Register tmpReg)]
                  else
                    []
              in
                compCode @ handleCode
              end
            else
              [(translateBop bop p, a64.Register target, a64.Register target, a64.Register e2Reg)]
        in
          e1Code @ e2Code @ bopCode
        end

      | Hermes.AllZero(x, exp, p) =>
        (*TODO: Skal der matches på loc -> hvor arrayet ligger?*)
        (*TODO: mangler vel at verify længden af arrayet*)
        (case exp of
          Hermes.Const (n, p1)=>
            let
              val (t, vReg) = lookup x env p1
              (* find byte size *)
              val (ldrOpcode, regSize, immSize) =
                case t of
                  Hermes.U8  => (a64.LDRB, a64.RegisterW, "1")
                | Hermes.U16 => (a64.LDRH, a64.RegisterW, "2")
                | Hermes.U32 => (a64.LDR,  a64.RegisterW, "4")
                | Hermes.U64 => (a64.LDR,  a64.Register,  "8")
              
              val tmpReg  = a64.newRegister ()
              val iReg    = a64.newRegister ()
              val orReg   = a64.newRegister ()

              (* TODO: can maybe use vReg instead of iReg
                  as vReg dies *)
              val initCode = [
                (a64.MOV, a64.Register orReg, a64.XZR, a64.NoOperand),
                (a64.MOV, a64.Register iReg, a64.Register vReg, a64.NoOperand)]
              val orCode =
                List.tabulate (HermesCx64.fromNumString n,
                  fn i => [
                    (ldrOpcode, regSize tmpReg, a64.APost(iReg, immSize), a64.NoOperand),
                    (a64.ORR, regSize orReg, regSize orReg, regSize tmpReg)
                  ])
              val testCode = [
                (a64.CMP, regSize orReg, a64.Imm 0, a64.NoOperand),
                (a64.CSETM, a64.Register target, a64.Cond a64.EQ, a64.NoOperand)
              ]
            in
              initCode @ List.concat orCode @ testCode
            end
          | _ => raise HermesCx64.Error("Array size should be costant after PE", p)
          )

      | _ => [(a64.LABEL ("compilExp:" ^ Hermes.showExp exp true), 
              a64.NoOperand, a64.NoOperand, a64.NoOperand)]

  (*  *)
  fun compileDecs [] env = ([], [], env)
    | compileDecs (Hermes.ConstDecl (_,_,pos) :: ds) env =
      raise HermesCx64.Error ("Constants should have been eliminated by PE", pos)
    | compileDecs (Hermes.VarDecl (x, (_, it), pos) :: ds) env =
      let
        val r = a64.newRegister ()
        val env1 = (x, (it, r)) :: env
        val (alloc, dealloc, env2) = compileDecs ds env1
      in
        (
          [(a64.EOR, a64.Register r, a64.Register r, a64.Register r)] @ alloc,
          dealloc,
          env2
        )
      end 
    | compileDecs (Hermes.ArrayDecl (x, (_, it), exp, pos) :: ds) env =
      case exp of
        Hermes.Const(n, p1) =>
        let
          val r = a64.newRegister ()
          val env1 = (x, (it, r)) :: env
          val (alloc, dealloc, env2) = compileDecs ds env1
          (* Find out which STR opcode to use *)
          val (strOpcode, regSize, immSize, zr) = 
            (case it of
              Hermes.U8    => (a64.STRB, a64.RegisterW, "1", a64.WZR)
              | Hermes.U16 => (a64.STRH, a64.RegisterW, "2", a64.WZR)
              | Hermes.U32 => (a64.STR, a64.RegisterW,  "4", a64.WZR)
              | Hermes.U64 => (a64.STR, a64.Register,   "8", a64.XZR)
            )
          val tmpReg = a64.newRegister ()
          val setupCode = [(a64.MOV, a64.Register tmpReg, a64.Register r, a64.NoOperand)]
          val clearCode =
            List.tabulate (HermesCx64.fromNumString n,
              fn i => (strOpcode, zr, a64.APost(tmpReg, immSize), a64.NoOperand))
          val arraySize = HermesCx64.fromNumString immSize * HermesCx64.fromNumString n 
          val alignment = arraySize + (arraySize mod 16)
          (* TODO: sub amount fits within imm optimization? *)
          val subReg = a64.newRegister ()
          val subCode = 
            [(a64.LDR, a64.Register subReg, a64.PoolLit (decToHex (Int.toString alignment)), a64.NoOperand)]

          (*stack pointer restore*)
          val restoreCode = [(a64.ADD, a64.SP, a64.SP, a64.Register subReg)]
        in
          (
            subCode @ [(a64.SUB, a64.SP, a64.SP, a64.Register subReg),
              (a64.MOV, a64.Register r, a64.SP, a64.NoOperand)]
              @ setupCode @ clearCode @ alloc,
              dealloc @ restoreCode,
              env2
          )
        end
      | _ => raise HermesCx64.Error ("Array size should be constant after PR", pos)
      

  fun compileStat stat env =
    (case stat of
      Hermes.Skip => []
      | Hermes.Update (uop, Hermes.UnsafeArray(s, i, p), e, pos) =>
        (* Whenever an update with a unsafe array convert it to a safe array *)
        compileStat (Hermes.Update (uop, Hermes.Array (s, i, p), e, pos)) env
      | Hermes.Update (uop, lval, e, pos) =>
        let
          val opc = translateUop uop
          val eReg = a64.newRegister ()
          val eCode = compileExp e eReg env pos

          (* t = type and resReg is register containing result *)
          val (loadCode, saveCode, t, resReg) =
            (case lval of
              Hermes.Var(n, p) =>
                let
                  val (t, vReg) = lookup n env p
                in
                  ([], [], t, vReg)
                end
              | Hermes.Array(s, i, p) =>
                (*TODO: Create loadcode for Array with constant index -> imm*)
                let
                  val (t, vReg) = lookup s env p
                  val iReg = a64.newRegister ()
                  val tmpReg = a64.newRegister ()
                  val iCode = compileExp i iReg env p
                  val (ldr, str, reg, size) = getForType t
                  val load = [
                    (a64.LDR, a64.Register tmpReg, a64.PoolLit (int2String size), a64.NoOperand),
                    (a64.MUL, a64.Register iReg, a64.Register iReg, a64.Register tmpReg),
                    (ldr, reg tmpReg, a64.ABaseOffR(vReg, iReg), a64.NoOperand)
                  ]
                  val save = (maskDown (reg tmpReg) t) @ [
                    (str, reg tmpReg, a64.ABaseOffR(vReg, iReg), a64.NoOperand)
                  ]
                in
                  (load, save, t, tmpReg)
                end
              | _ => ([],[],Hermes.U8,9999) (*Should never happen. To silence compiler*)
            )
          val updateCode =
            let
              val updCode = [(opc, a64.Register resReg, a64.Register resReg, a64.Register eReg)]
              val (setup, cleanup) =
                (case uop of
                    Hermes.RoR => (extendBits (a64.Register resReg) t, [])
                  | Hermes.RoL => 
                    let 
                      val setup   = extendBits (a64.Register resReg) t
                      val reverse = [(a64.RBIT, a64.Register resReg, a64.Register resReg, a64.NoOperand)]
                    in
                      (setup @ reverse, reverse)
                    end
                  | _ => ([], [])
                )
            in
              setup @ updCode @ cleanup
            end
        in
          eCode @ loadCode @ updateCode @ saveCode
        end
        (* ---------- end of Update ----------*)
      
      | Hermes.Block (dl, ss, pos) =>
        let
          val (code1, code2, env1) = compileDecs dl env
          val ssCode = List.map (fn s => compileStat s env1) ss
        in
          code1 @ List.concat ssCode @ code2
        end
        (* ---------- end of Block ----------*)

      | Hermes.Assert (e, (l,p)) =>
        let
          val eReg = a64.newRegister ()
          val eCode = compileExp e eReg env (l,p)
          val label = HermesCx64.makeName "label" (l,p)
        in
          eCode @ [
            (a64.CMP, a64.Register eReg, a64.Imm 0, a64.NoOperand),
            (a64.B a64.NE, a64.Label_ label, a64.NoOperand, a64.NoOperand),
            (a64.LDR, a64.Register eReg,
              a64.PoolLit (decToHex (a64.signedToString (10000*l+p))), a64.NoOperand),
            (a64.STR, a64.Register eReg, a64.ABaseOffI(a64.fp, "-144"), a64.NoOperand),
            (a64.B a64.NoCond, a64.Label_ "exit_label_", a64.NoOperand, a64.NoOperand),
            (a64.LABEL label, a64.NoOperand, a64.NoOperand, a64.NoOperand)
          ]
        end
        (* ---------- end of Assert ----------*)

      | Hermes.Swap (lv1, lv2, p) =>
        (case (lv1, lv2) of
        (Hermes.Var (x1, p1), Hermes.Var(x2, p2)) =>
          let
            val (t1, v1Reg) = lookup x1 env p1
            val (t2, v2Reg) = lookup x2 env p2
            val r1 = a64.newRegister ()
          in
            [(a64.EOR, a64.Register r1, a64.Register v1Reg, a64.Register v2Reg),
            (a64.AND, a64.Register v1Reg, a64.Register v1Reg, a64.Register r1),
            (a64.EOR, a64.Register v2Reg, a64.Register v2Reg, a64.Register r1),
            (a64.EOR, a64.Register r1, a64.Register r1, a64.Register r1)]
          end
        | (Hermes.Var (x1, p1), Hermes.Array(x2, Hermes.Const (i, p3), p2)) =>
          let 
            val (t1, v1Reg) = lookup x1 env p1
            val (t2, v2Reg) = lookup x2 env p2
            val size = type2Bytes t1
            val index = HermesCx64.fromNumString i
            val offset = size * index
            val offset1 = HermesCx64.signedToString offset
            val r1 = a64.newRegister()
            val r2 = a64.newRegister()
            val (ldr, str, reg) =
                (case t1 of
                  Hermes.U8    => (a64.LDRB, a64.STRB, a64.RegisterW)
                  | Hermes.U16 => (a64.LDRH, a64.STRH, a64.RegisterW)
                  | Hermes.U32 => (a64.LDR, a64.STR, a64.RegisterW)
                  | Hermes.U64 => (a64.LDR,  a64.STR,  a64.Register))
          in
            if offset > 32760 then
              [(a64.LDR, a64.Register r2, a64.PoolLit (decToHex offset1), a64.NoOperand), 
               (ldr, reg r1, a64.ABaseOffR(v2Reg, r2), a64.NoOperand),
               (str, reg v1Reg, a64.ABaseOffR(v2Reg, r2), a64.NoOperand),
               (a64.MOV, a64.Register v1Reg, a64.Register r1, a64.NoOperand),
               (a64.EOR, a64.Register r1, a64.Register r1, a64.Register r1)]
            else 
              [(ldr, reg r1, a64.ABaseOffI(v2Reg, offset1), a64.NoOperand),
               (str, reg v1Reg, a64.ABaseOffI(v2Reg, offset1), a64.NoOperand),
               (a64.MOV, a64.Register v1Reg, a64.Register r1, a64.NoOperand),
               (a64.EOR, a64.Register r1, a64.Register r1, a64.Register r1)]
          end
        | (Hermes.Array (y, Hermes.Const (n, p3), p2), Hermes.Var (x, p1)) =>
            compileStat
              (Hermes.Swap (Hermes.Var (x, p1),
                            Hermes.Array (y, Hermes.Const (n, p3), p2), p)) env
        | (Hermes.Array (x1, Hermes.Const (i1, p2), p1),
                        Hermes.Array (x2, Hermes.Const (i2, p4), p3)) =>
          let 
            val (t1, v1Reg) = lookup x1 env p1
            val (t2, v2Reg) = lookup x2 env p2
            val size = type2Bytes t1
            val index1 = HermesCx64.fromNumString i1 
            val index2 = HermesCx64.fromNumString i2 
            val offset1 = HermesCx64.signedToString (size * index1)
            val offset2 = HermesCx64.signedToString (size * index2)
            val r1 = a64.newRegister()
            val r2 = a64.newRegister()
            val r3 = a64.newRegister()
            val r4 = a64.newRegister()
            val (ldr, str, reg) =
              (case t1 of
                Hermes.U8    => (a64.LDRB, a64.STRB, a64.RegisterW)
                | Hermes.U16 => (a64.LDRH, a64.STRH, a64.RegisterW)
                | Hermes.U32 => (a64.LDR, a64.STR, a64.RegisterW)
                | Hermes.U64 => (a64.LDR,  a64.STR,  a64.Register))
          in
            (* TODO: immediate size offset*)  
            [(a64.LDR, a64.Register r1, a64.PoolLit (decToHex offset1), a64.NoOperand),
             (a64.LDR, a64.Register r2, a64.PoolLit (decToHex offset2), a64.NoOperand),
             (ldr, reg r3, a64.ABaseOffR(v1Reg, r1), a64.NoOperand),
             (ldr, reg r4, a64.ABaseOffR(v2Reg, r2), a64.NoOperand),
             (str, reg r3, a64.ABaseOffR(v2Reg, r2), a64.NoOperand),
             (str, reg r4, a64.ABaseOffR(v1Reg, r1), a64.NoOperand),
             (a64.EOR, a64.Register r3, a64.Register r3, a64.Register r3),
             (a64.EOR, a64.Register r4, a64.Register r4, a64.Register r4)]
          end
        | (Hermes.UnsafeArray (y, e, p2), lv) =>
          compileStat (Hermes.Swap (Hermes.Array (y, e, p2), lv, p)) env
        | (lv, Hermes.UnsafeArray (y, e, p2)) =>
          compileStat (Hermes.Swap (lv, Hermes.Array (y, e, p2), p)) env
        | _ => raise HermesCx64.Error ("unmatched swap case", p))
      (* ---------- end of Swap ----------*)
      
      | (Hermes.CondSwap (e, l1, l2, p)) =>
        let
          val condReg = a64.newRegister ()
          val tmpReg  = a64.newRegister ()
          val iReg    = a64.newRegister ()
          val i2Reg   = a64.newRegister ()
          val elmReg  = a64.newRegister ()
          val elm2Reg = a64.newRegister ()

          val condCode = compileExp e condReg env p @
            [(a64.CMP, a64.Register condReg, a64.Imm 0, a64.NoOperand),
            (a64.CSETM, a64.Register tmpReg, a64.Cond a64.NE, a64.NoOperand)]

          val clearCode = 
            [(a64.EOR, a64.Register tmpReg, a64.Register tmpReg, a64.Register tmpReg)]
          
          fun getSizes t =
              (case t of
                Hermes.U8    => (a64.LDRB, a64.STRB, a64.RegisterW, 1)
                | Hermes.U16 => (a64.LDRH, a64.STRH, a64.RegisterW, 2)
                | Hermes.U32 => (a64.LDR, a64.STR, a64.RegisterW,   4)
                | Hermes.U64 => (a64.LDR,  a64.STR,  a64.Register,  8))
          
          val lCode =
            (case (l1, l2) of
              (Hermes.Var(s1, p1), Hermes.Var(s2, p2)) =>
                let
                  val (t1, l1Reg) = lookup s1 env p1
                  val (t2, l2Reg) = lookup s2 env p2
                  val (ldr, str, reg, size) = getSizes t1
                in
                  [(a64.EOR, a64.Register tmpReg, a64.Register l1Reg, a64.Register l2Reg),
                  (a64.AND, a64.Register tmpReg, a64.Register condReg, a64.Register tmpReg),
                  (a64.EOR, a64.Register l1Reg, a64.Register l1Reg, a64.Register tmpReg),
                  (a64.EOR, a64.Register l2Reg, a64.Register l2Reg, a64.Register tmpReg)]
                end
              
              | (Hermes.Var(s1, p1), Hermes.Array(s2, (Hermes.Const(n, p3)), p2)) =>
                let
                  val (t1, l1Reg) = lookup s1 env p1
                  val (t2, l2Reg) = lookup s2 env p2
                  val (ldr, str, reg, size) = getSizes t1
                  val index = HermesCx64.fromNumString n
                  val offset = HermesCx64.signedToString (size * index)
 
                in
                [(a64.LDR, a64.Register iReg, a64.PoolLit offset, a64.NoOperand),
                   (ldr, reg elmReg, a64.ABaseOffR(l2Reg, iReg), a64.NoOperand),

                   (a64.EOR, a64.Register tmpReg, a64.Register l1Reg, a64.Register elmReg),
                   (a64.AND, a64.Register tmpReg, a64.Register condReg, a64.Register tmpReg),
                   (a64.EOR, a64.Register l1Reg, a64.Register l1Reg, a64.Register tmpReg),
                   (a64.EOR, a64.Register elmReg, a64.Register elmReg, a64.Register tmpReg),

                   (str, reg elmReg, a64.ABaseOffR(l2Reg, iReg), a64.NoOperand),
                   (a64.EOR, a64.Register elmReg, a64.Register elmReg, a64.Register elmReg)]
                end

              | (Hermes.Array(s1, e1, p1), Hermes.Var(s2, p2)) =>
                compileStat (Hermes.CondSwap (e, Hermes.Var(s2, p2), Hermes.Array(s1, e1, p1), p)) env
              
              | (Hermes.Array(s1, (Hermes.Const (n1, p3)), p1), 
                 Hermes.Array(s2, (Hermes.Const (n2, p4)), p2)) =>
                 let
                  val (t1, l1Reg) = lookup s1 env p1
                  val (t2, l2Reg) = lookup s2 env p2
                  val (ldr, str, reg, size) = getSizes t1
                  val index1 = HermesCx64.fromNumString n1
                  val index2 = HermesCx64.fromNumString n2
                  val offset1 = HermesCx64.signedToString (size * index1)
                  val offset2 = HermesCx64.signedToString (size * index2)

                in
                  [(a64.LDR, a64.Register iReg, a64.PoolLit offset1, a64.NoOperand),
                   (ldr, reg elmReg, a64.ABaseOffR(l1Reg, iReg), a64.NoOperand),

                  (a64.LDR, a64.Register i2Reg, a64.PoolLit offset2, a64.NoOperand),
                   (ldr, reg elm2Reg, a64.ABaseOffR(l2Reg, i2Reg), a64.NoOperand),

                   (a64.EOR, a64.Register tmpReg, a64.Register elm2Reg, a64.Register elmReg), 
                   (a64.AND, a64.Register tmpReg, a64.Register condReg, a64.Register tmpReg),
                   (a64.EOR, a64.Register elmReg, a64.Register elmReg, a64.Register tmpReg),
                   (a64.EOR, a64.Register elm2Reg, a64.Register elm2Reg, a64.Register tmpReg),

                   (str, reg elmReg, a64.ABaseOffR(l1Reg, iReg), a64.NoOperand),
                   (str, reg elm2Reg, a64.ABaseOffR(l2Reg, i2Reg), a64.NoOperand),
                   (a64.EOR, a64.Register elmReg, a64.Register elmReg, a64.Register elmReg),
                   (a64.EOR, a64.Register elm2Reg, a64.Register elm2Reg, a64.Register elm2Reg)]
                end
              | (Hermes.UnsafeArray (s1, e1, p1), lv) =>
                compileStat (Hermes.CondSwap (e, Hermes.Array(s1, e1, p1), lv, p)) env
              | (lv, Hermes.UnsafeArray (s1, e1, p1)) =>
                compileStat (Hermes.CondSwap (e, lv, Hermes.Array(s1, e1, p1), p)) env
            )

        in
          condCode @ lCode @ clearCode
        end
      (* ---------- end of CondSwap ----------*)

      | _ => (* Should never happen only for debugging *)
        [(a64.LABEL ("compileStat: " ^ debugStat stat), 
          a64.NoOperand, a64.NoOperand, a64.NoOperand)]
    )

  fun compileA64Args [] locs = ([], [], [])
      | compileA64Args _ [] =
          raise HermesCx64.Error ("Not enough parameter locations", (0,0))
      | compileA64Args (Hermes.VarArg (x, (_, it), _) :: args) (l1 :: locs) =
          let
            val (env, code1, code2) = compileA64Args args locs
            val r = a64.newRegister ()
            val r1 = a64.newRegister ()

            val (ldrOpcode, strOpcode, regSize) =
              (case it of
                  Hermes.U8  => (a64.LDRB, a64.STRB, a64.RegisterW)
                | Hermes.U16 => (a64.LDRH, a64.STRH, a64.RegisterW)
                | Hermes.U32 => (a64.LDR, a64.STR, a64.RegisterW)
                | Hermes.U64 => (a64.LDR, a64.STR, a64.Register)
              )

            val (locCode1, locCode2) = 
              (case l1 of
                a64.ABaseOffI (_, _) => 
                  ([(a64.LDR, a64.Register r1, l1, a64.NoOperand),
                    (ldrOpcode, regSize r, a64.ABase r1, a64.NoOperand)],
                   [(strOpcode, regSize r, a64.ABase r1, a64.NoOperand)]
                  )
                | _ => 
                  ([(a64.MOV, a64.Register r1, l1, a64.NoOperand), (* can maybe delete *)
                    (ldrOpcode, regSize r, a64.ABase r1, a64.NoOperand)],
                   [(strOpcode, regSize r, a64.ABase r1, a64.NoOperand)]
                  )
              )
          in
            (* call by value result *)
            (* TODO: update to load to register *)
            ((x, (it, r)) :: env,
            locCode1 @ code1,
            code2 @ locCode2)
          end
      | compileA64Args (Hermes.ArrayArg (x, (_, it), _) :: args) (l1 :: locs) =
          let
            val (env, code1, code2) = compileA64Args args locs
            val r = a64.newRegister ()
            val (locCode1, locCode2) = 
              (case l1 of
                a64.ABaseOffI (_, _) => 
                  ([(a64.LDR, a64.Register r, l1, a64.NoOperand)],
                   [(a64.STR, a64.Register r, l1, a64.NoOperand)]
                  )
                | _ => 
                  ([(a64.MOV, a64.Register r, l1, a64.NoOperand)],
                   [(a64.MOV, l1, a64.Register r, a64.NoOperand)]
                  )
              )
          in
            ((x,(it, r)) :: env,
            locCode1 @ code1,
            code2 @ locCode2)
          end

(* generates code to zero the input list of fp offsets in memory *)
fun zeroOffsets [] = []
  | zeroOffsets (offset :: offsets) =
    let 
      val offsetsZeroed = zeroOffsets offsets
    in
      [(a64.LDR, a64.Register 9, a64.PoolLit offset, a64.NoOperand),
       (a64.STR, a64.XZR, a64.ABaseOffR(a64.fp, 9), a64.NoOperand)] 
       :: offsetsZeroed
    end

(* generates code to zero the input list of registers *)
fun zeroRegisters [] = []
  | zeroRegisters (reg :: regs) =
    let
      val regsZeroed = zeroRegisters regs
    in
      (a64.EOR, a64.Register reg, a64.Register reg, a64.Register reg) :: regsZeroed
    end

(* create list of unused parameter registers *)
(* takes number of used parameter registers as input *)
fun unusedParaRegisters regVal =
    if regVal > 7 orelse regVal < 1 then [] 
    else 
      let
        val regs = unusedParaRegisters (regVal + 1)
      in
        regVal :: regs
      end
(* update SP to correct offset after reg allocator *)
fun replaceSPOff [] offset = []
  | replaceSPOff ((a64.REPLACESP, _, _, _) :: instrs) offset =
    let
      val absOffset = Int.abs offset
      val alignment = absOffset + (absOffset mod 16)
    in 
      if alignment > 4095 then
        ((a64.LDR, a64.Register 9, a64.PoolLit (decToHex (Int.toString alignment)), a64.NoOperand) ::
        (a64.SUB, a64.SP, a64.Register a64.fp, a64.Imm alignment) :: instrs)
      else
        ((a64.SUB, a64.SP, a64.Register a64.fp, a64.Imm alignment) :: instrs)
    end
  | replaceSPOff (instr :: instrs) offset =
        instr :: replaceSPOff instrs offset

  fun compileProcedure f args body =
    let
      val parameterLocations =
        List.map a64.Register a64.argRegs @
        List.map (fn n => a64.ABaseOffI(a64.fp, n)) 
                  ["-16","-24","-32","-40","-48"] 
      val arglist = HermesCx64.compileCArgs args
      val (env, prologue1, epilogue0) = compileA64Args args parameterLocations
      val saveCallee = (* save callee-saves variables *)
            [(a64.STR, a64.Register 19, a64.ABaseOffI (a64.fp, "-56"), a64.NoOperand),
            (a64.STR, a64.Register 20, a64.ABaseOffI (a64.fp, "-64"), a64.NoOperand),
            (a64.STR, a64.Register 21, a64.ABaseOffI (a64.fp, "-72"), a64.NoOperand),
            (a64.STR, a64.Register 22, a64.ABaseOffI (a64.fp, "-80"), a64.NoOperand),
            (a64.STR, a64.Register 23, a64.ABaseOffI (a64.fp, "-88"), a64.NoOperand),
            (a64.STR, a64.Register 24, a64.ABaseOffI (a64.fp, "-96"), a64.NoOperand),
            (a64.STR, a64.Register 25, a64.ABaseOffI (a64.fp, "-104"), a64.NoOperand),
            (a64.STR, a64.Register 26, a64.ABaseOffI (a64.fp, "-112"), a64.NoOperand),
            (a64.STR, a64.Register 27, a64.ABaseOffI (a64.fp, "-120"), a64.NoOperand),
            (a64.STR, a64.Register 28, a64.ABaseOffI (a64.fp, "-128"), a64.NoOperand),
            (* save SP, USE PSEUDO-REG INSTEAD? *)
            (a64.MOV, a64.Register 9, a64.SP, a64.NoOperand),
            (a64.STR, a64.Register 9, a64.ABaseOffI (a64.fp, "-136"), a64.NoOperand),
            (* error code *)
            (a64.STR, a64.XZR, a64.ABaseOffI (a64.fp, "-144"), a64.NoOperand),
            (* placeholder for moving SP *)
            (a64.REPLACESP, a64.NoOperand, a64.NoOperand, a64.NoOperand)] 
      val bodyCode = compileStat body env
      val epilogue1 =
            [(a64.LABEL ("exit_label_"), a64.NoOperand, a64.NoOperand, a64.NoOperand),
            (a64.LDR, a64.Register 0, a64.ABaseOffI (a64.fp, "-144"), a64.NoOperand)]
      val restoreCallee = (* restore callee-saves variables *)
            [(a64.LDR, a64.Register 19, a64.ABaseOffI (a64.fp, "-56"), a64.NoOperand),
            (a64.LDR, a64.Register 20, a64.ABaseOffI (a64.fp, "-64"), a64.NoOperand),
            (a64.LDR, a64.Register 21, a64.ABaseOffI (a64.fp, "-72"), a64.NoOperand),
            (a64.LDR, a64.Register 22, a64.ABaseOffI (a64.fp, "-80"), a64.NoOperand),
            (a64.LDR, a64.Register 23, a64.ABaseOffI (a64.fp, "-88"), a64.NoOperand),
            (a64.LDR, a64.Register 24, a64.ABaseOffI (a64.fp, "-96"), a64.NoOperand),
            (a64.LDR, a64.Register 25, a64.ABaseOffI (a64.fp, "-104"), a64.NoOperand),
            (a64.LDR, a64.Register 26, a64.ABaseOffI (a64.fp, "-112"), a64.NoOperand),
            (a64.LDR, a64.Register 27, a64.ABaseOffI (a64.fp, "-120"), a64.NoOperand),
            (a64.LDR, a64.Register 28, a64.ABaseOffI (a64.fp, "-128"), a64.NoOperand),
            (* restore SP *)
            (a64.LDR, a64.Register 9, a64.ABaseOffI (a64.fp, "-136"), a64.NoOperand),
            (a64.MOV, a64.SP, a64.Register 9, a64.NoOperand)]
      
      (* Zero Caller-Saved registers *)
      (* x9 - x15 and unused parameter registers *)
      val callerSavedToZero = unusedParaRegisters (List.length args) @ a64.callerSaves
      val epilogue3 = zeroRegisters callerSavedToZero

      val allCode =
            prologue1 @ saveCallee  @ bodyCode  @
      epilogue0 @ epilogue1 @ restoreCallee @ epilogue3
      val _ = TextIO.output (TextIO.stdErr, "instructions before: " ^ (Int.toString (List.length allCode)) ^ "\n")
      val _ = TextIO.output (TextIO.stdErr, "pseudo registers: " ^ (Int.toString (a64.newRegister() - 32)) ^ "\n")
      val (newCode, offset, offsetsToZero) = a64.registerAllocate allCode
      val newCode1 = replaceSPOff newCode (offset)
      val _ = TextIO.output (TextIO.stdErr, "instructions after: " ^ (Int.toString (List.length allCode)) ^ "\n")
    in
      "int " ^ f ^ "(" ^ arglist ^ ")\n" ^
      "{\n  asm volatile ( \n" ^
      String.concat (List.map a64.printInstruction newCode1) ^
      "  );\n}\n\n"
    end 
end