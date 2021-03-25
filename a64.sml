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
    = Register  of int              (*64 bit*)
    | RegisterW of int              (*32 bit*)        
    | Constant  of string
    | Literal   of string
    | ImmOffset of int * string     (* adresss = register + offset *)
    | RegAddr   of int              (* register address to ldr/str *)
    | Imm       of int
    | BaseOffset of operand * operand
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
    | showOperand (Literal n) = "=0x" ^ n
    | showOperand (ImmOffset (r, off)) =
      (*TODO: immediate size check?*)
      let
        val regNum = Int.toString r
      in
        "[X" ^ regNum ^ ", #" ^ off ^ "]" 
      end
   | showOperand (RegAddr r) =
      let
        val regNum = Int.toString r
      in
        "[X" ^ regNum ^ "]"
      end
    | showOperand SP = "SP"
    | showOperand noOperand = ""
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


end
