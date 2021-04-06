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

  datatype operand
    = Register  of int          (*64 bit*)
    | RegisterW of int          (*32 bit*)

    | Imm       of int          (* #imm *)
    | PoolLit   of string          (* Pool Literal *)
    
    (* Addressing modes *)
    | ABase     of int          (* [base] *)
    | ABaseOffR of int * int    (* [base, Rm] *)
    | ABaseOffI of int * string    (* [base, #imm] *)
    | APre      of int * string    (* [base, #imm]! *)
    | APost     of int * string    (* [base], #imm *)

    (* Specials *)
    | SP 
    | NoOperand

  datatype opcode 
    = LDR | STR
    | LDRB | STRB     (* <--                             *)
    | LDRH | STRH     (* <-- Remember to use W registers!*)
    | LDRW | STRW     (* <--                             *)
    | LABEL of string (*not an actual opcode*)
    | ROR
    | EOR
    | ADD | SUB
    | LSL
    | ORR
    | MOV
    | AND
    | RBIT
    | MUL

  type inst = opcode * operand * operand * operand 



  fun showOperand (Register r) =
      let val regNum = Int.toString r in 
        "X" ^ regNum
      end
    | showOperand (RegisterW r) =
      let val regNum = Int.toString r in
        "W" ^ regNum
      end
    (* | showOperand Constant (s) = *)
    | showOperand (PoolLit n) = "=0x" ^ n
    | showOperand (ABaseOffI (r, off)) =
      (*TODO: immediate size check?*)
      let
        val regNum = Int.toString r
      in
        "[X" ^ regNum ^ ", #" ^ off ^ "]" 
      end
   | showOperand (ABase r) =
      let
        val regNum = Int.toString r
      in
        "[X" ^ regNum ^ "]"
      end
    | showOperand SP = "SP"
    | showOperand NoOperand = ""
    | showOperand _ = "missing case in showOperand"

  fun showOpcode LDR = "LDR "
    | showOpcode STR = "STR "
    | showOpcode LDRB = "LDRB "
    | showOpcode STRB = "STRB "
    | showOpcode LDRH = "LDRH "
    | showOpcode STRH = "STRH "
    | showOpcode LDRW = "LDRW "
    | showOpcode STRW = "STRW "
    | showOpcode MOV = "MOV "
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
  fun setUnion2 [] = Splayset.empty pairOrder
    | setUnion2 [s] = s
    | setUnion2 (s :: ss) =
       Splayset.union (setUnion2 ss, s)

  (* reference to list of spilled data *)      
  val spilled = ref []

  fun regsRead operand =
    case operand of
      Register r => [r]
    | RegisterW r => [r]
    | ImmOffset (r, _) => [r]
    | RegAddr r => [r]
    | BaseOffset (r1, r2) => [r1, r2]
    | _ => []

  fun regsWritten operand =
    case operand of 
      Register r => [r]
    | _ => []

  (* regs read by i, so live at start of i *)
  fun generateLiveness instr =
    let 
      val (opc, op1, op2, op3) = instr
    in 
      case opc of
        (* STR only op that reads from op1*)
        STR => list2set(regsRead op1 @ regsRead op2)
        (* others can be generalized to read from op2 and op3 *)
      | _ =>  list2set(regsRead op2 @ regsRead op3)
    end
  
  fun killLiveness instr =
    let
      val (opc, dest, _, _) = instr
    in
      case opc of
        STR => emptyset
      | _ => list2set(regsWritten dest)
    end

  (* registers live at exit from instructions *)
  fun liveness instrs gen kill =
    let val (liveOut, _) = liveness1 instrs gen kill
    in 
      liveOut
    end
  
  (* Liveness analysis, determine out and in set*)
  (* simple one pass because of PE *)
  (* JMPS for error conditions? *)
  fun liveness1 instrs gen kill =
    case (instrs, gen, kill) of
      ((opc, _, _, _) :: ins, g :: gs, k :: ks) =>
        let 
          val (live1, liveOut) = liveness1 ins gs ks
          val liveIn = setUnion [setMinus liveOut k, g]
        in 
          (liveOut :: live1, liveIn)
        end
      | _ => ([], emptyset)

  (* find pairs of interfering registers *)
  (* follows Torbens structure, but could make it tail recursive? *)
  fun interfere instrs liveOut kill =
    case (instrs, live, kill) of
      ((opc, _, _, _) :: ins, lOut :: ls, k :: ks) =>
        setUnion2[interfere ins ls ks]


    | _ => list2set []


  fun findUses [] = Splaymap.mkDict Int.compare
    | findUses (inst :: instrs) =
      let
        val uses = findUses instrs
        val regs = Splayset.listItems
                    (setUnion [generateLiveness inst, killLiveness inst])
      in
        List.foldl(fn (r, u) => case Splaymap.peek (u, r) of (* peek: u = map, r = key, returns val *)
	                    NONE => Splaymap.insert (u,r,1) (*  *)
	                  | SOME c => Splaymap.insert (u,r,c+1))
            uses regs
	end
        
  fun registerAllocate instrs = 
    let 
      val _ = spilled := []
      val uses = findUses instrs
      val gen = List.map generateLiveness instrs (* liveness generation *)
      val kill = List.map killLiveness instrs   (* liveness killed *)
      val liveOut = liveness instrs gen kill       (* propagation *)
      val interference0 = interfere instrs liveOut kill
      val interference = Splayset.listItems interference0
    in

    end
end
