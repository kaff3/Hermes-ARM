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
    
    val argRegs = [0,1,2,3,4,5,6,7,8]
    val returnRegs = [0,1,2,3,4,5,6,7,8]
    val calleeSaves = [19, 20, 21, 22, 23, 24, 25, 26, 27, 28]
    val fp = 29
    val zr = 31

    datatype operand = Register of int * int (* reg, w/x *)
                | Constant of string
                | Literal of string
                | Label of string
                | ImmOffset of int * string (* adresss = register + offset *)
                | SP
                | FP
                | NoOperand
z
    datatype opcode = LDR 
                | STR

    type inst = opcode * operand * operand * operand 
    


