(* Types for A64 *)
structure a64 =
struct

  exception Error of string

  val argRegs = [0, 1, 2, 3, 4, 5, 6, 7]
  val returnRegs = [0,1,2,3,4,5,6,7]
  val callerSaves = [8,9,10,11,12,13,14,15,16,17]
  val calleeSaves = [19, 20, 21, 22, 23, 24, 25, 26, 27, 28]
  val fp = 29
  val allocatableRegs = argRegs @ callerSaves @ calleeSaves

  (* Used for pseudo-registers*)
  val regCounter = ref 31

  fun newRegister () =
    (regCounter := !regCounter + 1;
     !regCounter)

  datatype cond
    = EQ | NE
    | HI  (* x > y  *)
    | LS  (* x <= y *)
    | NoCond

  datatype opcode
    (* memory *) 
    = LDR  | STR
    | LDRB | STRB 
    | LDRH | STRH    
    (* arithmic *)
    | ADD | SUB
    | MUL
    (* logic *)
    | ROR
    | EOR
    | LSL | LSR
    | ORR | AND
    | MOV | MVN
    | RBIT
    | CMP
    | CSETM
    | B of cond
    | NEG
    (* not actual opcodes *)
    | LABEL of string
    | REPLACESP 

  datatype operand
    = Register  of int             (*64 bit*)
    | RegisterW of int             (*32 bit*)

    | Imm       of int             (* #imm *)
    | PoolLit   of string          (* Pool Literal *)
    
    (* Addressing modes *)
    | ABase     of int             (* [base] *)
    | ABaseOffR of int * int       (* [base, Rm] *)
    | ABaseOffI of int * string    (* [base, #imm] *)
    | APre      of int * string    (* [base, #imm]! *)
    | APost     of int * string    (* [base], #imm *)

    | Shifted of int * opcode * int     (* reg * <LSL|LSR> amount *)

    (* Specials *)
    | Cond of cond
    | Label_ of string
    | SP 
    | XZR
    | WZR
    | NoOperand

  type inst = opcode * operand * operand * operand 

  fun showCondition EQ = "EQ"
    | showCondition NE = "NE"
    | showCondition HI = "HI"
    | showCondition LS = "LS"
    | showCondition NoCond = ""

  fun showOpcode LDR = "LDR "
    | showOpcode STR = "STR "
    | showOpcode LDRB = "LDRB "
    | showOpcode STRB = "STRB "
    | showOpcode LDRH = "LDRH "
    | showOpcode STRH = "STRH "
    
    | showOpcode ADD = "ADD "
    | showOpcode SUB = "SUB "
    | showOpcode MUL = "MUL "

    | showOpcode ROR = "ROR "
    | showOpcode EOR = "EOR "
    | showOpcode LSL = "LSL "
    | showOpcode LSR = "LSR "
    | showOpcode ORR = "ORR "
    | showOpcode MOV = "MOV "
    | showOpcode MVN = "MVN "
    | showOpcode AND = "AND "
    | showOpcode RBIT = "RBIT "
    | showOpcode CMP = "CMP "
    | showOpcode CSETM = "CSETM "
    | showOpcode NEG = "NEG "
    | showOpcode (B c) = 
      let
        val dot = 
          (case c of
            NoCond => ""
            | _ =>  "."
          )
      in
        "B"^ dot ^ showCondition c ^ " "
      end
    | showOpcode _ = "missing case in showOpcode"

  fun showOperand (Register r) =
      let val regNum = Int.toString r in 
        "X" ^ regNum
      end
    | showOperand (RegisterW r) =
      let val regNum = Int.toString r in
        "W" ^ regNum
      end
    | showOperand (Imm i) = "#" ^ (Int.toString i)
    | showOperand (PoolLit n) = 
      if String.isPrefix "0x" n then
        "=" ^ n
      else
        "=0x" ^ n
    | showOperand (ABaseOffI (r, off)) =
      let
        val regNum = Int.toString r
      in
        "[X" ^ regNum ^ ", #" ^ off ^ "]" 
      end
   | showOperand (ABaseOffR (r1, r2)) =
    let 
      val reg1 = Int.toString r1
      val reg2 = Int.toString r2
    in
      "[X" ^ reg1 ^ ", X"^ reg2 ^ "]" 
    end
   | showOperand (ABase r) =
      let
        val regNum = Int.toString r
      in
        "[X" ^ regNum ^ "]"
      end
    | showOperand (APost (r, i)) =
      let
        val regNum = Int.toString r
      in
        "[X" ^ regNum ^ "], #" ^ i
      end
    | showOperand (Cond c) = showCondition c
    | showOperand (Label_ s) = s
    | showOperand SP = "SP"
    | showOperand XZR = "XZR"
    | showOperand WZR = "WZR"
    | showOperand NoOperand = ""
    | showOperand (Shifted (r, _, a)) = 
      let
        val reg = (Int.toString r) 
        val amount = (Int.toString a)
      in
        "X" ^ reg ^ "," ^ "LSL " ^ "#" ^ amount
      end
    | showOperand _ = "missing case in showOperand"


  fun printInstruction (opc, op1, op2, op3) =
    (case opc of
      (LABEL l) => "\"" ^ l ^ ":\\n\\t\"\n"
      | _ =>
        let
          val [c2, c3] = List.map (fn n => case n of NoOperand => " " | _ => ", ") [op2, op3]
          val opc = showOpcode opc
          val op1 = " " ^ (showOperand op1)
          val op2 = c2 ^ (showOperand op2)
          val op3 = c3 ^ (showOperand op3)
        in 
          "\"" ^ opc ^ op1 ^ op2 ^ op3 ^ "\\n\\t\"\n"
        end
    )
  
  (* REGISTER ALLOCATOR *)
  (* helper functions *)
  fun setUnion [] = Binaryset.empty Int.compare
    | setUnion [s] = s
    | setUnion (s :: ss) = Binaryset.union (setUnion ss, s)

  val emptyset = Binaryset.empty Int.compare

  fun setMinus xs ys = Binaryset.difference (xs, ys)

  fun list2set ll = Binaryset.addList (Binaryset.empty Int.compare, ll)

  fun pairOrder ((x1,y1), (x2,y2)) =
    if x1 < x2 orelse x1 = x2 andalso y1 < y2 then LESS
    else if x1 = x2 andalso y1 = y2 then EQUAL
    else GREATER

  (* used for Binarysets of pairs *)
  fun setUnionP [] = Binaryset.empty pairOrder
    | setUnionP [s] = s
    | setUnionP (s :: ss) =
       Binaryset.union (setUnionP ss, s)

  fun list2setP ll = Binaryset.addList (Binaryset.empty pairOrder, ll)

  fun signedToString n = (if n<0 then "-" else "") ^ Int.toString (Int.abs n)

  (* register-to-register moves *)
  fun getMoves instr =
    case instr of
      (MOV, op1, op2, _) =>
        (case (op1, op2) of 
          (Register x, Register y) => list2setP [(x,y), (y,x)]
        | (Register x, RegisterW y) => list2setP [(x,y), (y,x)]
        | (RegisterW x, Register y) => list2setP [(x,y), (y,x)]
        | (RegisterW x, RegisterW y) => list2setP [(x,y), (y,x)]
        | _ => list2setP []
        )
    | _ => list2setP []

  (* reference to list of spilled data *)      
  val spilled = ref []

  fun regsRead operand =
    case operand of
      Register r => [r]
    | RegisterW r => [r]
    | ABase r => [r]
    | ABaseOffI (r, _) => [r]
    | ABaseOffR (r1, r2) => [r1, r2]
    | APre (r, _) => [r]
    | APost (r, _) => [r]
    | Shifted (r, _, _) => [r]
    | _ => []

  fun regsWritten operand =
    case operand of 
      Register r => [r]
    | RegisterW r => [r]
    | _ => []

  fun addrModesWritten operand =
    case operand of 
      APre (r, _) => [r]
    | APost (r, _) => [r]
    | _ => []

  (* regs read by i, so live at start of i *)
  fun generateLiveness instr =
    case instr of 
      (EOR, _, op2, op3) =>
        if op2 = op3 then emptyset
        else list2set(regsRead op2 @ regsRead op3)
    | (opc, op1, op2, op3) =>
        (case opc of
          STR => list2set(regsRead op1 @ regsRead op2)
          | STRB => list2set(regsRead op1 @ regsRead op2)
          | STRH => list2set(regsRead op1 @ regsRead op2)
          | CMP => list2set(regsRead op1 @ regsRead op2)
          (* others can be generalized to read from op2 and op3 *)
        | _ =>  list2set(regsRead op2 @ regsRead op3))
    
  
  (* regs written to by i, so live at end of i *)
  fun killLiveness instr =
    let
      val (opc, dest, addrOp, _) = instr
    in
      case opc of
        STR => list2set(addrModesWritten addrOp)
        | STRB => list2set(addrModesWritten addrOp)
        | STRH => list2set(addrModesWritten addrOp)
        | CMP => emptyset
      | _ => list2set(regsWritten dest @ addrModesWritten addrOp)
    end

  (* Liveness analysis, determine out and in set*)
  (* simple one pass because of PE *)
  fun liveness1 instrs gen kill =
    case (instrs, gen, kill) of
      ((opc, op1, _, _) :: ins, g :: gs, k :: ks) =>
        let 
          val (live1, liveOut, labels) = liveness1 ins gs ks
          val liveIn = 
            case ((opc, op1)) of
              (B c, Label_ l) => 
                (case (c) of 
                  NoCond => labels l (* unconditional jump *) 
                  | _ => setUnion [liveOut, labels l]
                )
              | _ => setUnion [setMinus liveOut k, g]
          val labels1 = (* update label mapping *)
            case opc of
              LABEL l1 => (fn l => if l=l1 then liveIn else labels l)  
              | _ => labels
        in 
          (liveOut :: live1, liveIn, labels1)
        end
      | _ => ([], emptyset, (fn l => raise Error ("label " ^ l ^ " not found\n")))
  

  (* registers live at exit from instructions *)
  fun liveness instrs gen kill =
    let val (liveOut, _, _) = liveness1 instrs gen kill
    in 
      liveOut
    end
  
  (* find pairs of interfering registers *)
  (* reg x interferes with y if x in kill[i] and y in out[i] for inst i *)

  fun interfere instrs liveOut kill =
    case (instrs, liveOut, kill) of
      ((MOV, op1, op2, _) :: ins, lOut :: ls, k :: ks) =>
        (case (op1, op2) of
        (Register x, Register y) => 
          setUnionP[interfere ins ls ks, list2setP(List.concat (List.map 
            (fn z => [(x, z), (z, x)]) (Binaryset.listItems (setMinus lOut (list2set [x,y])))))] 
        | (Register x, RegisterW y) => 
          setUnionP[interfere ins ls ks, list2setP(List.concat (List.map 
              (fn z => [(x, z), (z, x)]) (Binaryset.listItems (setMinus lOut (list2set [x,y])))))]
        | (RegisterW x, Register y) => 
          setUnionP[interfere ins ls ks, list2setP(List.concat (List.map 
              (fn z => [(x, z), (z, x)]) (Binaryset.listItems (setMinus lOut (list2set [x,y])))))]
        | (RegisterW x, RegisterW y) => 
          setUnionP[interfere ins ls ks, list2setP(List.concat (List.map 
              (fn z => [(x, z), (z, x)]) (Binaryset.listItems (setMinus lOut (list2set [x,y])))))]
        | _ => 
          setUnionP[interfere ins ls ks, list2setP(List.concat(List.map
              (fn x => List.concat (List.map (fn y => [(x, y), (y,x)]) 
                      (Binaryset.listItems (setMinus lOut (list2set [x])))))
                      (Binaryset.listItems k)))]
        )
      | (_ :: ins, lOut :: ls, k :: ks) =>
        setUnionP[interfere ins ls ks, list2setP(List.concat(List.map
            (fn x => List.concat (List.map (fn y => [(x, y), (y,x)]) 
                    (Binaryset.listItems (setMinus lOut (list2set [x])))))
                    (Binaryset.listItems k)))]
      | _ => list2setP []

  (* find node with fewest neighbours *)
  fun fewestNeighbours [] (x,ys) = (x,ys)
    | fewestNeighbours ((x1,ys1) :: neighbours) (x,ys) =
      if List.length ys1 < List.length ys then 
        fewestNeighbours neighbours (x1,ys1)
      else fewestNeighbours neighbours (x,ys)

  (* remove node from graph *)
  fun remove x [] = []
    | remove x ((x1,ys) :: neighbours) =
         if x=x1 then remove x neighbours
	 else (x1, List.filter (fn y => y<>x) ys) :: remove x neighbours

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


  val allocatable = list2set (allocatableRegs)
  val numAllocatable = List.length (allocatableRegs)

  (* select step of graph colouring *)
  fun select [] moves mapping = mapping
    | select ((x,ys) :: stack) moves mapping =
      let
        val ys1 = list2set (List.map mapping ys)
        val freeRegs = setMinus allocatable ys1 (* minus registers used by neighbours *)
        
        (* look for move instruction x:=y where*)
        (* if y already has been assigned a register and does not interfere with x *)
        (* can then use same register and will increase num of assignments to be removed *)
        (* determine if (x, mapping y) is a pair in moves and if mapping y is in freeregs*)
        
        val moveRelated = Binaryset.find 
              (fn (x1, y1) => x1 = x andalso Binaryset.member (freeRegs, (mapping y1))) moves
        val freeRegs1 = Binaryset.listItems freeRegs

        val selected =
          case (moveRelated, freeRegs1) of
            (SOME (_ , y), _) => mapping y
          | (_, y :: ys) => y
          | _ => (spilled := x :: !spilled; x)
      
      in
	      select stack moves (fn y => if x=y then selected else mapping y)
	    end

  (* find best spill candidate *)
  fun bestSpill [] uses (x,ys,score) = (x,ys)
    | bestSpill ((x1,ys1) :: neighbours) uses (x,ys,score) =
      let
        val _ = TextIO.output (TextIO.stdErr, "looking for spill \n")
        val usesOfx1 = Binarymap.find (uses,x1)
        val score1 = (10000 * List.length ys1) div (usesOfx1 + 1)
      (* many neighbours and few uses is better *)
	    in
        if score1 > score
        then bestSpill neighbours uses (x1,ys1,score1)
        else bestSpill neighbours uses (x,ys,score)
      end

  fun simplify [] stack moves uses = select stack moves (fn x => x)
    | simplify ((x,ys) :: neighbours) stack moves uses =
      let  
        val (x1, ys1) = fewestNeighbours neighbours (x,ys) (* ys = neighbours *)
        val (x2, ys2) = 
              if List.length ys1 < numAllocatable then (x1, ys1) (* colourable *)
              else bestSpill ((x,ys) :: neighbours) uses (x,ys,~1) (* find spill candidate *)
        val neighbours1 = remove x2 ((x,ys) :: neighbours)
	    in
        simplify neighbours1 ((x2,ys2) :: stack) moves uses
	    end

  fun colourGraph interference moves uses =
    let
      (* finds all pseudoregisters a given pseudoreg interferes with *)
      val interferesWith =
            List.filter (fn (x,ys) => x > 31) (pairs2map interference)
    in
      simplify interferesWith [] moves uses
    end

  (* map pseudo registers to new registers *)
  fun reColour mapping (opc, op1, op2, op3) =
    (opc, reColourOp mapping op1, reColourOp mapping op2,  reColourOp mapping op3)


  and reColourOp mapping oper =
    case oper of
      Register r => Register (mapping r)
    | RegisterW r => RegisterW (mapping r)
    | Imm x => Imm x
    | PoolLit x => PoolLit x 
    | ABase r => ABase (mapping r)
    | ABaseOffR (r1, r2) => ABaseOffR (mapping r1, mapping r2)
    | ABaseOffI (r, x) => ABaseOffI (mapping r, x)
    | APre (r, x) => APre (mapping r, x)
    | APost (r, x) => APost (mapping r, x)
    | Cond c => Cond c 
    | Label_ s => Label_ s 
    | SP => SP
    | XZR => XZR
    | WZR => WZR
    | Shifted (r, _, a) => Shifted (mapping r, LSL, a)
    | NoOperand => NoOperand

  fun notSelfMove inst = 
    case inst of
    (MOV, op1, op2, _) => 
      (case (op1, op2) of 
        (Register x, Register y) => x<>y
      | (Register x, RegisterW y) => x<>y
      | (RegisterW x, Register y) => x<>y
      | (RegisterW x, RegisterW y) => x<>y
      | _ => true
      )
    | _ => true

  (* FUNCTIONS FOR SPILLING *)
  val spillOffset = ref (~152)
  val usedOffsets = ref []
  
  fun replaceRegOp x x1 ope =
    case ope of
      Register y => if x=y then Register x1 else ope
    | RegisterW y => if x=y then RegisterW x1 else ope
    | ABase y => if x = y then ABase x1 else ope
    | ABaseOffI (y, i) => if x = y then ABaseOffI (x1, i) else ope
    | ABaseOffR (y, z) =>
        ABaseOffR (if x = y then x1 else y, if x = z then x1 else z)
    | APre (y, z) => if x = y then APre (x1, z) else ope
    | APost (y, z) => if x = y then APost (x1, z) else ope
    | Shifted (r, _, a) => if x = r then Shifted (x1, LSL, a) else ope
    | _ => ope

  fun replaceReg x x1 (opc, op1, op2, op3) =
    (opc, replaceRegOp x x1 op1, replaceRegOp x x1 op2, replaceRegOp x x1 op3)

  fun spill x offset [] = []
    | spill x offset (instr :: instrs) =
      let
        val reads1 = generateLiveness instr
        val reads = Binaryset.member (reads1, x)
        val writes1 = killLiveness instr
        val writes = Binaryset.member (writes1,x)
        val instrs1 = spill x offset instrs
        val x1 = newRegister ()
	    in
        case (reads, writes) of
          (false, false) => instr :: instrs1
        | (true, false) =>
            (LDR, Register x1, ABaseOffI (fp, offset), NoOperand)
            :: (replaceReg x x1 instr)
            :: instrs1
        | (false, true) =>
            (replaceReg x x1 instr)
            :: (STR, Register x1, ABaseOffI (fp, offset), NoOperand)
            :: instrs1
        | (true, true) =>
            (LDR, Register x1, ABaseOffI (fp, offset), NoOperand)
            :: (replaceReg x x1 instr)
            :: (STR, Register x1, ABaseOffI (fp, offset), NoOperand)
            :: instrs1
	    end

  fun spillList [] instrs = instrs
    | spillList (x :: xs) instrs =
      let
        val _ = TextIO.output
                 (TextIO.stdErr, "spill register " ^ Int.toString x ^ "\n")
        val offset = signedToString (spillOffset := !spillOffset - 8; !spillOffset)
        (* add the offset to list of used offsets to be zeroed later *)
        val instrs1 = spill x offset instrs
	    in
	      usedOffsets := offset :: !usedOffsets; spillList xs instrs1
	    end


  fun findUses [] = Binarymap.mkDict Int.compare
    | findUses (inst :: instrs) =
      let
        val uses = findUses instrs
        val regs = Binaryset.listItems
                    (setUnion [generateLiveness inst, killLiveness inst])
      in
        List.foldl(fn (r, u) => case Binarymap.peek (u, r) of 
	                    NONE => Binarymap.insert (u,r,1) 
	                  | SOME c => Binarymap.insert (u,r,c+1))
            uses regs
	end

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


  fun registerAllocate instrs = 
    let 
      val _ = spilled := []
      val gen = List.map generateLiveness instrs           (* liveness generation *)
      val kill = List.map killLiveness instrs              (* liveness killed *)
      val liveOut = liveness instrs gen kill               (* propagation *)
      val interference0 = interfere instrs liveOut kill    (* interference: pairs of overlapping pseudoregs *)
      val interference = Binaryset.listItems interference0
      val uses = findUses instrs                   
      val moves = setUnionP (List.map getMoves instrs)     (* find move instructions *)
      val mapping = colourGraph interference moves uses
    in
      if null (!spilled) then
        let
          val newInstrs = List.map (reColour mapping) instrs
          val withoutSelf = List.filter notSelfMove newInstrs
        in
          (withoutSelf, !spillOffset - 8, !usedOffsets)
        end
      else
      (* if we have spilled variables, do register allocation again *)
        registerAllocate (spillList (!spilled) instrs)
    end
end
