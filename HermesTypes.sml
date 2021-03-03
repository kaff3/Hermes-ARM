structure HermesTypes :> HermesTypes =
struct

  exception Error of string*(int*int)

  (* lookup in environment *)
  fun lookup x [] pos =
        raise Error ("undeclared identifier " ^ x, pos)
    | lookup x ((y,v) :: env) pos =
        if x = y then v else lookup x env pos

  (* check if value is in list *)
  fun isIn x xs = List.exists (fn y => x = y) xs

  datatype valType = Secret | Public

  fun showValType Secret = "secret "
    | showValType Public = "public "

  (* translate Hermes.valType to valType *)
  fun translateType Hermes.Public = Public
    | translateType Hermes.Secret = Secret

  (* least upper bound of valTypes *)
  fun sqcup Public Public = Public
    | sqcup _ _ = Secret

  (* ordering on valTypes *)
  fun sqleq t1 t2 = t2 = sqcup t1 t2

  (* integer sizes *)
  datatype iSize = u8 | u16 | u32 | u64

  fun showSize u8 = "8 "
    | showSize u16 = "16 "
    | showSize u32 = "32 "
    | showSize u64 = "64 "

  (* translate Hermes.intType to iSize *)
  fun translateSize Hermes.U8 = u8
    | translateSize Hermes.U16 = u16
    | translateSize Hermes.U32 = u32
    | translateSize Hermes.U64 = u64

  type sizedType = valType * iSize

  fun showST (v,z) = showValType v ^ showSize z

  (* variable types *)
  datatype varType = Constant
                   | Scalar of sizedType
                   | ArrayOf of sizedType

  fun showVarType Constant = "const"
    | showVarType (Scalar zt) = showST zt
    | showVarType (ArrayOf zt) = showST zt ^ "[]"

  (* variables in expressions (excluding x in size x) *)
  fun V (Hermes.Const (n,p)) = []
    | V (Hermes.Rval (Hermes.Var (x, p))) = [x]
    | V (Hermes.Rval (Hermes.Array (x, e, p))) = x :: V e
    | V (Hermes.Rval (Hermes.UnsafeArray (x, e, p))) = x :: V e
    | V (Hermes.Un (uop, e, p)) = V e
    | V (Hermes.Bin (bop, e1, e2, p)) = V e1 @ V e2
    | V (Hermes.Size (x, p)) = []
    | V (Hermes.AllZero (x, e, p)) = x :: V e

  (* root variable of L-value *)
  fun R (Hermes.Var (x, p)) = x
    | R (Hermes.Array (x, e, p)) = x
    | R (Hermes.UnsafeArray (x, e, p)) = x

  (* variables in index expression of L-value *)
  fun V_I (Hermes.Var (x, p)) = []
    | V_I (Hermes.Array (x, e, p)) = V e
    | V_I (Hermes.UnsafeArray (x, e, p)) = V e

  (* variables that are updated in statement *)
  fun U Hermes.Skip = []
    | U (Hermes.Update (uop, lv, e, p)) = [R lv]
    | U (Hermes.Swap (lv1, lv2, p)) = [R lv1, R lv2]
    | U (Hermes.CondSwap (e, lv1, lv2, p)) = [R lv1, R lv2]
    | U (Hermes.If (e, s1, s2, p)) = U s1 @ U s2
    | U (Hermes.For (x, e1, e2, s, p)) =
          List.filter (fn y => y <> x) (U s)
    | U (Hermes.Call (f, lvs, p)) = List.map R lvs
    | U (Hermes.Uncall (f, lvs, p)) = List.map R lvs
    | U (Hermes.Block (ds, ss, p)) =
          let
	    val xs = D ds
	    val ys = List.concat (List.map U ss)
	  in
            List.filter (fn y => not (List.exists (fn x => x=y) xs)) ys
	  end
    | U (Hermes.Assert (e, p)) = []

  and D [] = []
    | D (Hermes.ConstDecl (x, n, p)::ds) = x :: D ds
    | D (Hermes.VarDecl (x, t, p)::ds) = x :: D ds
    | D (Hermes.ArrayDecl (x, t, e, p)::ds) = x :: D ds

  fun intersect [] ys = []
    | intersect (x :: xs)  ys =
        if List.exists (fn y => y=x) ys then x :: intersect xs ys
	else  intersect xs ys

  (* time-variant binary operations *)
  val TV = [Hermes.Divide, Hermes.Modulo]

  (* check L-value, |-_L rules*)
  (* Note: returns position as well as varType for error reporting *)
  fun check_L rho (Hermes.Var (x, p)) = (* (Variable) *)
        (lookup x rho p, p)
    | check_L rho (Hermes.Array (x, e, p)) = (* (ArrayAcces) *)
        (case lookup x rho p of
           ArrayOf tz => 
             if check_E rho e = Public then
               (Scalar tz, p)
             else
               raise Error ("index expression is not public", p)
         | _ => raise Error (x ^ " is not an array", p))
    | check_L rho (Hermes.UnsafeArray (x, e, p)) = (* (Unsafe ArrayAcces) *)
        (case lookup x rho p of
           ArrayOf (Secret, z) => 
             let val t = check_E rho e in
               (Scalar (Secret, z), p)
	     end
         | _ =>
	     raise Error ("unsafe acces to public array or non-array " ^ x, p))

  (* check expression, |-_E rules *)
  and check_E rho (Hermes.Const (n, p)) = Public (* (Constant1) *)
    | check_E rho (Hermes.Rval l) =
        (case check_L rho l of
           (Constant, p) => Public (* (Constant2) *)
         | (Scalar (t,z), p) => t  (* (L-val) *)
         | (ArrayOf tz, p) => raise Error ("expression can not be array", p))
    | check_E rho (Hermes.Un (uop, e, p)) = check_E rho e (* (UnOp) *)
    | check_E rho (Hermes.Bin (bop, e1, e2, p)) =
        if sqcup (check_E rho e1) (check_E rho e2) = Secret (* (BinOp2) *)
        then
          if not (isIn bop TV) then Secret
          else raise Error ("time-variant operation on secret values", p)
        else Public (* (BinOp1) *)
    | check_E rho (Hermes.Size (x, p)) = (* (Size) *)
        (case lookup x rho p of
           ArrayOf st => Public
         | _  => raise Error (x ^ " is not an array", p))
    | check_E rho (Hermes.AllZero (x, e, p)) =
        (case lookup x rho p of
           ArrayOf tz => 
             if check_E rho e = Public then Public
             else
               raise Error ("size expression is not public", p)
         | _ => raise Error (x ^ " is not an array", p))

  (* check if declared argument matches passed parameter. *)
  (* Used in Call rule *)
  fun checkArg (vartype1, (vartype2, p)) =
        if vartype1 = vartype2 then ()
        else raise Error ("parameter type does not match declaration", p)

  (* verify that variable i does not occur in list j for i<>j. *)
  (* Used in Call rule *)
  fun notIn [] vls errMess p = ()
    | notIn (v :: vs) vls errMess p =
        let
          val m = List.length vs
          val n = List.length vls
          val vls1 = List.take (vls, n-m-1) @ List.drop (vls, n-m)
        in
          if List.exists (isIn v) vls1 then
            raise Error (v ^ errMess, p)
          else notIn vs vls errMess p
        end

  (* check declarations, |-_D rules *)
  fun check_D rho [] = rho  (* (EmptyDecl) *)
    | check_D rho (Hermes.ConstDecl (x, n, p) :: d) =  (* (ConstDecl) *)
         check_D ((x, Constant) :: rho) d
    | check_D rho (Hermes.VarDecl (x, (t,z), p) :: d) = (* (VarDecl) *)
        check_D ((x, Scalar (translateType t, translateSize z)) :: rho) d
    | check_D rho (Hermes.ArrayDecl (x, (t,z), e, p) :: d) = (* (ArrayDecl) *)
        if check_E rho e = Public then
          check_D ((x, ArrayOf (translateType t, translateSize z)) :: rho) d
        else
          raise Error ("size of array " ^ x ^ " must be public", p)

  (* check statements, |-_S rules *)
  fun check_S gamma rho (Hermes.Skip) = () (* (Empty) *)
    | check_S gamma rho (Hermes.Update (uop, l, e, p)) = (* (Update) *)
        let
          val (lt, _) = check_L rho l
          val t1 = check_E rho e
        in
          case lt of
            Scalar (t0,s) =>
              if isIn (R l) (V e) then
                raise Error ("Root of L-value can not occur in expression", p)
              else if isIn (R l) (V_I l) then
                raise Error ("Root of L-value can not occur in its own index expression", p)
              else if not (sqleq t1 t0) then
                raise Error ("public L-value updated with secret value", p)
              else ()
          | _ => raise Error ("Can not update constants or arrays", p)
        end
    | check_S gamma rho (Hermes.Swap (l1, l2, p)) = (* (Swap) *)
        (case (check_L rho l1, check_L rho l2) of
           ((Scalar tz1,_), (Scalar tz2,_)) =>
             if tz1 <> tz2 then
               raise Error ("swapped L-values must have same type", p)
             else if isIn (R l1) (V_I l2) orelse isIn (R l2) (V_I l1) then
               raise Error ("root of L-value can not occur in index of swapped L-value", p)
             else ()
         | (_, _) =>  raise Error ("can not swap constants or arrays", p))
    | check_S gamma rho (Hermes.CondSwap (c, l1, l2, p)) = (* (SwapC) *)
        (case (check_L rho l1, check_L rho l2, check_E rho c) of
           ((Scalar (t0,z0),_), (Scalar (t1,z1),_), t2) =>
             if  (t0,z0) <> (t1,z1) then
               raise Error ("swapped L-values must have same type", p)
             else if isIn (R l1) (V_I l2) orelse isIn (R l2) (V_I l1) then
               raise Error ("root of L-value can not occur in index of swapped L-value", p)
             else if not (sqleq t2 t0) then
               raise Error ("secret condition used to swap public values", p)
             else if isIn (R l1) (V c) orelse isIn (R l2) (V c) then
               raise Error ("root of L-value can not occur in condition", p)
             else ()
         | (_, _, _) => raise Error ("can not swap constants or arrays", p))
    | check_S gamma rho (Hermes.If (e, s1, s2, p)) =
        (case check_E rho e of
	   Public =>
	     let
	       val () = check_S gamma rho s1
	       val () = check_S gamma rho s2
	       val vs = V e
	       val u1 = U s1
	       val u2 = U s2
	     in
	       case intersect vs (u1 @ u2) of
	         [] => ()
               | (x :: _) =>
	           raise Error
		          ("condition variable " ^ x ^ " updated in branch", p)
	     end
	 | _ => raise Error ("condition must be public", p))
    | check_S gamma rho (Hermes.For (x, e1, e2, s, p)) = (* (ForLoop) *)
        let
	  val vs1 = V e1
	  val vs2 = V e2
	  val u = U s
	in
          case (check_E rho e1, check_E rho e2, intersect (vs1 @ vs2) u) of
            (Public, Public, []) =>
               check_S gamma ((x, Scalar (Public, u64)) :: rho) s
          | (Public, Public, _) =>
	       raise Error ("variables in loop bounds can not be updated in body", p)
          | (_, _, _) => raise Error ("loop bounds must be public", p)
	end
    | check_S gamma rho (Hermes.Call (f, ls, p)) = (* (Call) *)
        let
          val args = lookup f gamma p
          val lts = List.map (check_L rho) ls
          val as_lts = ListPair.zip (args, lts)
          val roots = List.map R ls
          val vars = List.map (V o Hermes.Rval) ls
        in
          if List.length args <> List.length lts then
            raise Error ("wrong number of arguments", p)
          else
            (List.app checkArg as_lts ;
	     if List.exists (fn l => isIn (R l) (V_I l)) ls
	     then raise Error ("parameter root can not occur in its own index", p)
	     else ();
             notIn roots vars " occurs in another parameter" p) 
        end
    | check_S gamma rho (Hermes.Uncall (f, ls, p)) = (* (UnCall) *)
         check_S gamma rho (Hermes.Call (f, ls, p))
    | check_S gamma rho (Hermes.Block (d, ss, p)) = (* (Block) *)
        let
          val rho1 = check_D rho d
        in
          List.app (check_S gamma rho1) ss
        end
    | check_S gamma rho (Hermes.Assert (e, p)) =
        let val t = check_E rho e in () end

  (* check argument declarations, |-_A rules *)
  fun check_A rho [] = rho
    | check_A rho (Hermes.VarArg (x, (t,z), p) :: a) = (* (Scalar) *)
        (let val _ = lookup x rho p in
           raise Error (x ^ " declared twice in argument list", p)
         end
         handle Error _ =>
           check_A (rho@[(x, Scalar (translateType t, translateSize z))]) a)
    | check_A rho (Hermes.ArrayArg (x, (t,z), p) :: a) = (* (Array) *)
        (let val _ = lookup x rho p in
           raise Error (x ^ " declared twice in argument list", p)
         end
         handle Error _ =>
           check_A (rho@[(x, ArrayOf (translateType t, translateSize z))]) a)

  (* check procedure, |-_P rule *)
  fun check_P (f, a, s, p) = (* (Procedure1) *)
    let
      val rho = check_A [] a
    in
      (f, List.map (#2) rho)
    end

  (* check procedure, |-^P rule *)
  fun check'P gamma (f, a, s, p) = (* (Procedure2) *)
    let
      val rho = check_A [] a
    in
      check_S gamma rho s
    end

  (* check program, |- rule *)
  fun check p = (* (Program) *)
    let
      val gamma = List.map check_P p
      val pNames = List.map (#1) gamma
    in
      notIn pNames (List.map (fn n => [n]) pNames) " is declared twice " (0,0);
      List.app (check'P gamma) p
    end

end
