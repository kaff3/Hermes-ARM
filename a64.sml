(* Types for A64 *)


structure a64 =
struct

  exception Error of string

  val genRegs = [["W0", "X0"], ["W1", "X1"],
              ["W2", "X2"], ["W3", "X3"],
              ["W4", "X4"], ["W5", "X5"],
              ["W6", "X6"], ["W7", "X7"],
              ["W8", "X8"], ["W9", "X9"],
              ["W10", "X10"], ["W11", "X11"],
              ["W12", "X12"], ["W13", "X13"],
              ["W14", "X14"], ["W15", "X15"],
              ["W16", "X16"], ["W17", "X17"],
              ["W18", "X18"], ["W19", "X19"],
              ["W20", "X20"], ["W21", "X21"],
              ["W22", "X22"], ["W23", "X24"],
              ["W24", "X24"], ["W25", "X25"],
              ["W26", "X26"], ["W27", "X27"],
              ["W28", "X28"], ["W29", "X29"],
              ["W30", "X30"]] (* 31: WZR/XZR/WSP/SP *)
              (* TODO pseudo registers? *)
  
  val argRegs = [0, 1, 2, 3, 4, 5, 6, 7, 8]
  val returnRegs = [0,1,2,3,4,5,6,7,8]
  val calleeSaves = [19, 20, 21, 22, 23, 24, 25, 26, 27, 28]
  val fp = 29
  val zr = 31

  (* Used for pseudo-registers*)
  val regCounter = ref 31

  fun newRegister () =
    (regCounter := !regCounter + 1;
     !regCounter)

  (* datatype ext 
    = UXTW
    | UXTX
    | NoExt *)

  datatype cond
    = EQ | NE
    | HI  (* x > y  *)
    | LS  (* x <= y *)
    | NoCond

  datatype operand
    = Register  of int          (*64 bit*)
    | RegisterW of int          (*32 bit*)

    | Imm       of int          (* #imm *)
    | PoolLit   of string          (* Pool Literal *)
    
    (* Addressing modes *)
    | ABase     of int             (* [base] *)
    | ABaseOffR of int * int       (* [base, Rm] *)
    | ABaseOffI of int * string    (* [base, #imm] *)
    | APre      of int * string    (* [base, #imm]! *)
    | APost     of int * string    (* [base], #imm *)

    (* Specials *)
    | Cond of cond
    | Label_ of string
    | SP 
    | NoOperand

  datatype opcode
    (* memory *) 
    = LDR  | STR
    | LDRB | STRB     (* <--                             *)
    | LDRH | STRH     (* <-- Remember to use W registers!*)
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
    | LABEL of string (*not an actual opcode*)

  type inst = opcode * operand * operand * operand 

  fun showCondition EQ = "EQ"
    | showCondition NE = "NE"
    | showCondition HI = "HI"
    | showCondition LS = "LS"
    | showCondition NoCond = ""

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
      (*TODO: immediate size check?*)
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
    | showOperand NoOperand = ""
    | showOperand _ = "missing case in showOperand"

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
    | showOpcode ORR = "ORR "
    | showOpcode MOV = "MOV "
    | showOpcode AND = "AND "
    | showOpcode RBIT = "RBIT "

    | showOpcode CMP = "CMP "
    | showOpcode CSETM = "CSETM "
    | showOpcode (B c) = "B." ^ showCondition c ^ " "

    | showOpcode (LABEL s) = s
    | showOpcode _ = "missing case in showOpcode"

  fun printInstruction (opc, op1, op2 ,op3) =
    case opc of
      (LABEL l) => "\"" ^ l ^ "\\n\\t\"\n"
      | _ =>
        let
          val [c2, c3] = List.map (fn n => case n of NoOperand => " " | _ => ", ") [op2, op3]
          val opc = showOpcode opc
          val op1 = " " ^ (showOperand op1)
          val op2 = c2 ^ (showOperand op2)
          val op3 = c3 ^ (showOperand op3)
        in 
          (* Test if label or something else. Set comma accordingly  *)
          "\"" ^ opc ^ op1 ^ op2 ^ op3 ^ "\\n\\t\"\n"
        end
  
  (* Register allocator helper functions *)
  fun setUnion [] = Splayset.empty Int.compare
    | setUnion [s] = s
    | setUnion (s :: ss) = Splayset.union (setUnion ss, s)

  val emptyset = Splayset.empty Int.compare

  fun setMinus xs ys = Splayset.difference (xs, ys)

  fun list2set ll = Splayset.addList (Splayset.empty Int.compare, ll)

  fun pairOrder ((x1,y1), (x2,y2)) =
    if x1 < x2 orelse x1 = x2 andalso y1 < y2 then LESS
    else if x1 = x2 andalso y1 = y2 then EQUAL
    else GREATER

  (* used for splaysets of pairs *)
  fun setUnionP [] = Splayset.empty pairOrder
    | setUnionP [s] = s
    | setUnionP (s :: ss) =
       Splayset.union (setUnionP ss, s)

  fun list2setP ll = Splayset.addList (Splayset.empty pairOrder, ll)

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
    | _ => []

  fun regsWritten operand =
    case operand of 
      Register r => [r]
    | RegisterW r => [r]
    | _ => []

  (* regs read by i, so live at start of i *)
  fun generateLiveness instr =
    let 
      val (opc, op1, op2, op3) = instr
    in 
      case opc of
        (* STR only op that reads from op1*)
        STR => list2set(regsRead op1 @ regsRead op2)
        | STRB => list2set(regsRead op1 @ regsRead op2)
        | STRH => list2set(regsRead op1 @ regsRead op2)
        (* others can be generalized to read from op2 and op3 *)
      | _ =>  list2set(regsRead op2 @ regsRead op3)
    end
  
  (* regs written to by i, so live at end of i *)
  fun killLiveness instr =
    let
      val (opc, dest, _, _) = instr
    in
      case opc of
        STR => emptyset
        | STRB => emptyset
        | STRH => emptyset
        | CMP => emptyset
      | _ => list2set(regsWritten dest)
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
            case op1 of
              Label_ l1 => (fn l => if l=l1 then liveIn else labels l)  
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
  (* VI SKAL OGSÅ TJEKKE FOR REGISTERW det bliver bare grimt *)
  (* reg x interferes with y if x in kill[i] and y in out[i] for inst i *)

  fun interfere instrs liveOut kill =
    case (instrs, liveOut, kill) of
      ((MOV, op1, op2, _) :: ins, lOut :: ls, k :: ks) =>
        (case (op1, op2) of
        (Register x, Register y) => 
          setUnionP[interfere ins ls ks, list2setP(List.concat (List.map 
            (fn z => [(x, z), (z, x)]) (Splayset.listItems (setMinus lOut (list2set [x,y])))))] 
        | (Register x, RegisterW y) => 
          setUnionP[interfere ins ls ks, list2setP(List.concat (List.map 
              (fn z => [(x, z), (z, x)]) (Splayset.listItems (setMinus lOut (list2set [x,y])))))]
        | (RegisterW x, Register y) => 
          setUnionP[interfere ins ls ks, list2setP(List.concat (List.map 
              (fn z => [(x, z), (z, x)]) (Splayset.listItems (setMinus lOut (list2set [x,y])))))]
        | (RegisterW x, RegisterW y) => 
          setUnionP[interfere ins ls ks, list2setP(List.concat (List.map 
              (fn z => [(x, z), (z, x)]) (Splayset.listItems (setMinus lOut (list2set [x,y])))))]
        | _ => 
          setUnionP[interfere ins ls ks, list2setP(List.concat(List.map
              (fn x => List.concat (List.map (fn y => [(x, y), (y,x)]) 
                      (Splayset.listItems (setMinus lOut (list2set [x])))))
                      (Splayset.listItems k)))]
        )
      | (_ :: ins, lOut :: ls, k :: ks) =>
        setUnionP[interfere ins ls ks, list2setP(List.concat(List.map
            (fn x => List.concat (List.map (fn y => [(x, y), (y,x)]) 
                    (Splayset.listItems (setMinus lOut (list2set [x])))))
                    (Splayset.listItems k)))]
      | _ => list2setP []

  (* find node with fewest neighbours *)
  fun fewestNeighbours [] (x,ys) = (x,ys)
    | fewestNeighbours ((x1,ys1) :: neighbours) (x,ys) =
        if List.length ys1 < List.length ys
	then fewestNeighbours neighbours (x1,ys1)
	else fewestNeighbours neighbours (x,ys)

  (* registers that can be allocated -- NOT FP (29)*)
  (* maybe not r16-r18 and r30 *)
  (* https://wiki.cdot.senecacollege.ca/wiki/AArch64_Register_and_Instruction_Quick_Start *)
  (* remember to also change in other places then *)

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


  val allocatable = list2set (argRegs @ [9,10,11,12,13,14,15] @ calleeSaves)

  (* select step of graph colouring *)
  fun select [] moves mapping = mapping
    | select ((x,ys) :: stack) moves mapping =
      let
        val ys1 = list2set (List.map mapping ys)
        val freeRegs =
              Splayset.listItems (setMinus allocatable ys1) (* minus registers used by neighbours *)
        val moveRelated = List.filter
            (fn y => List.exists (fn (x1,y1) => (x1,mapping y1) = (x,y)) moves)freeRegs
        val selected =
          case (moveRelated, freeRegs) of
            (y :: ys, _) => y
          | ([], y :: ys) => y
          | ([], []) => (spilled := x :: !spilled; x)
      in
	      select stack moves (fn y => if x=y then selected else mapping y)
	    end

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

  fun simplify [] stack moves uses = select stack moves (fn x => x)
    | simplify ((x,ys) :: neighbours) stack moves uses =
      let
        val (x1, ys1) = fewestNeighbours neighbours (x,ys) (* ys = neighbours *)
        val (x2, ys2) = 
              if List.length ys1 < 26 then (x1, ys1) (* colourable , see allocatable *)
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

  val spillOffset = ref (~152)
  
  (* FOR SPILLED VARIABLES *)
  (* fun replaceRegOp x x1 ope =
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
        val offset = signedToString (spillOffset := !spillOffset - 8; !spillOffset)
        val instrs1 = spill x offset instrs
	    in
	      spillList xs instrs1
	    end *)


  fun findUses [] = Splaymap.mkDict Int.compare
    | findUses (inst :: instrs) =
      let
        val uses = findUses instrs
        val regs = Splayset.listItems
                    (setUnion [generateLiveness inst, killLiveness inst])
      in
        List.foldl(fn (r, u) => case Splaymap.peek (u, r) of 
	                    NONE => Splaymap.insert (u,r,1) 
	                  | SOME c => Splaymap.insert (u,r,c+1))
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
      val uses = findUses instrs                   
      val gen = List.map generateLiveness instrs    (* liveness generation *)
      val kill = List.map killLiveness instrs       (* liveness killed *)
      val liveOut = liveness instrs gen kill        (* propagation *)
      val interference0 = interfere instrs liveOut kill (* interference: pair of overlapping *)
      val interference = Splayset.listItems interference0
      val moves = Splayset.listItems (setUnionP (List.map getMoves instrs)) (* find move instructions *)
      val mapping = colourGraph interference moves uses
      (* val _ = TextIO.output(TextIO.stdErr, "INTERFERENCE: \n") 
      val _ = printGraph interference
      val _ = TextIO.output(TextIO.stdErr, "MAPPING: \n") 
      val _ = printMapping mapping *)
    in
      if null (!spilled) then
        let
          val newInstrs = List.map (reColour mapping) instrs
          val withoutSelf = List.filter notSelfMove newInstrs
        in
          (newInstrs, !spillOffset - 16)
        end
      else
      (* if we have spilled variables, do register allocation again *)
        (* registerAllocate (spillList (!spilled) instrs) *)
        registerAllocate instrs
    end
end
