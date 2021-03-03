structure Hermes =
struct

  (* types for abstract syntax for Hermes *)

  type pos = int * int  (* position: line, column *)

  datatype binOp
    = Plus | Minus | Times | Divide | Modulo
    | Xor | BAnd | BOr | ShiftL | ShiftR
    | Equal | Less | Greater | Neq | Leq | Geq

  datatype unOp = Negate

  datatype updateOp = Add | Sub | XorWith | RoL | RoR

  datatype lVal
    = Var of string * pos
    | Array of string * exp * pos
    | UnsafeArray of string * exp * pos

  and exp
    = Const of string * pos
    | Rval of lVal 
    | Un of unOp * exp * pos
    | Bin of binOp * exp * exp * pos
    | Size of string * pos
    | AllZero of string * exp * pos

  datatype intType = U8 | U16 | U32 | U64

  datatype valType = Secret | Public

  type varType = valType * intType

  datatype decl
    = ConstDecl of string * string * pos
    | VarDecl of string * varType * pos
    | ArrayDecl of string * varType * exp * pos

  datatype stat
    = Skip
    | Update of updateOp * lVal * exp * pos
    | Swap of lVal * lVal * pos
    | CondSwap of exp * lVal * lVal * pos
    | If of exp * stat * stat * pos
    | For of string * exp * exp * stat * pos (* update is part of body *)
    | Call of string * lVal list * pos
    | Uncall of string * lVal list * pos
    | Block of decl list * stat list * pos
    | Assert of exp * pos

  datatype arg
    = VarArg of string * varType * pos
    | ArrayArg of string * varType * pos

  type procedure = string * arg list * stat * pos

  type program = procedure list

  (* invert update operator *)
  fun invertUpOp upOp =
    case upOp of
      Add => Sub
    | Sub => Add
    | XorWith => XorWith
    | RoL => RoR
    | RoR => RoL

  (* reverse statement *)
  fun R s =
    case s of
       Update (upOp, lv, e, p) => Update (invertUpOp upOp, lv, e, p)
    | If (e, s1, s2, p) => If (e, R s1, R s2, p)
    | For (x, e1, e2, s, p) => For (x, e2, e1, R s, p)
    | Call args => Uncall args
    | Uncall args => Call args
    | Block (ds, ss, p) => Block (ds, List.rev (List.map R ss), p)
    | s => s (* skip, swap, condswap, assert *)

(* printing syntax *)

  fun showBinOp Plus = " + "
    | showBinOp Minus = " - "
    | showBinOp Times = " * "
    | showBinOp Divide = " / "
    | showBinOp Modulo = " % "
    | showBinOp Xor = " ^ "
    | showBinOp BAnd = " & "
    | showBinOp BOr  = " | "
    | showBinOp ShiftL = " << "
    | showBinOp ShiftR = " >> "
    | showBinOp Equal = " == "
    | showBinOp Less = " < "
    | showBinOp Greater = " > "
    | showBinOp Neq = " != "
    | showBinOp Leq = " <= "
    | showBinOp Geq = " >= "

  fun showUnOp Negate = " ~"

  fun showUpdateOp Add = " += "
    | showUpdateOp Sub = " -= "
    | showUpdateOp XorWith = " ^= "
    | showUpdateOp RoL = " <<= "
    | showUpdateOp RoR = " >>= "

  fun showLVal (Var (x,p)) = x
    | showLVal (Array (x,e,p)) = x ^ "[" ^ showExp e false ^ "]"
    | showLVal (UnsafeArray (x,e,p)) =
        "unsafe " ^ x ^ "[" ^ showExp e false ^ "]"

  and showLVals ls = String.concat (List.map (fn x => showLVal x ^ ", ") ls)

  (* 2nd argument tells whether parens are needed for compound expressions *)

  and showExp (Rval l) _ = showLVal l
    | showExp (Const (s,p)) _ = s
    | showExp (Bin (bop, e1, e2, p)) true =
         "(" ^ showExp e1 true ^ showBinOp bop ^ showExp e2 true ^ ")"
    | showExp (Bin (bop, e1, e2, p)) false =
         showExp e1 true ^ showBinOp bop ^ showExp e2 true
    | showExp (Un (uop, e1, p)) true =
         "(" ^ showUnOp uop ^ showExp e1 true ^ ")"
    | showExp (Un (uop, e1, p)) false =
         showUnOp uop ^ showExp e1 true
    | showExp (Size (x, p)) true = "(size " ^ x ^")"
    | showExp (Size (x, p)) false = "size " ^ x
    | showExp (AllZero (x,e,p)) _ =
        "allZero " ^ x ^ "[" ^ showExp e false ^ "]"

  fun showIntType  U8 = "u8 "
    | showIntType U16 = "u16 "
    | showIntType U32 = "u32 "
    | showIntType U64 = "u64 "

  fun showValType Public = "public "
    | showValType Secret = "secret "

  fun showVarType (vt, it) = showValType vt ^ showIntType it

  fun showDecl (VarDecl (x,t,p)) = showVarType t ^ x
    | showDecl (ConstDecl (x,v,p)) =
        "const " ^ x ^ " = " ^ v
    | showDecl (ArrayDecl (x,t,e,p)) =
        showVarType t ^ x ^ "[" ^ showExp e false ^ "]"

  fun showStat Skip = ";"
    | showStat (Update (uop, lv, e, p)) =
         showLVal lv ^ showUpdateOp uop ^ showExp e false ^ ";\n"
    | showStat (Swap (lv1, lv2, p)) =
         showLVal lv1 ^ " <-> " ^ showLVal lv2 ^ ";\n"
    | showStat (CondSwap (exp, lv1, lv2, p)) =
         "if (" ^ showExp exp false ^ ") " ^
         showLVal lv1 ^ " <-> " ^ showLVal lv2 ^ ";\n"
    | showStat (If (exp, s1, s2, p)) =
         "if (" ^ showExp exp false ^ ") " ^
	 showStat s1 ^ " else " ^ showStat s2
    | showStat (For (x, e1, e2, s, p)) =
         "for (" ^ x ^ " = " ^ showExp e1 false ^ ";" ^
         showExp e2 false ^ ")\n" ^ showStat s
    | showStat (Call (f, xs, p)) =
         "call " ^ f ^ "(" ^
         let
           val args = String.concat (List.map (fn x => showLVal x ^ ", ") xs)
         in
           String.substring (args, 0, String.size args - 2)
         end ^ ");\n"
    | showStat (Uncall (f, xs, p)) =
         "uncall " ^ f ^ "(" ^
         let
           val args = showLVals xs
         in
           String.substring (args, 0, String.size args - 2)
         end ^ ");\n"
    | showStat (Block (ds, ss, p)) =
         "{\n" ^
         String.concat (List.map (fn d => showDecl d ^ ";\n") ds) ^
         String.concat (List.map showStat ss) ^
         "}\n"
    | showStat (Assert (e, p)) =
         "assert " ^ showExp e false ^ ";\n"

  fun showArg (VarArg (x,t,p)) = showVarType t ^ x
    | showArg (ArrayArg (x,t,p)) =
        showVarType t ^ x ^ "[]"

  fun showProcedure (f, aas, s, p) =
         f ^ "(" ^
         let
           val args = String.concat (List.map (fn a => showArg a ^ ", ") aas)
         in
           if args = "" then ""
           else String.substring (args, 0, String.size args - 2)
         end ^ ")\n" ^ showStat s ^ "\n"

  fun showProgram ps =
         String.concat (List.map showProcedure ps)

end
