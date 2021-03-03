(* Hermes interpreter *)

structure HermesInt :> HermesInt =
struct

  open BigInt;;
  
  exception Error of string*(int*int)

  (* lookup in environment *)
  fun lookup x [] pos =
        raise Error ("undeclared identifier" ^ x, pos)
    | lookup x ((y,v) :: env) pos =
        if x = y then v else lookup x env pos


  datatype location = Variable of hex ref
                    | Array of int * hex array
                    | ArrayElement of int * hex array
                    | NullLocation

  type sizedLocation = hex * location

  (* the store is implicit, so the following functions *)
  (* do not take stores as inputs or outputs *)

  fun newlocation z = (z, Variable (ref []))

  (* takes a position as extra argument for error reporting *)
  fun disposelocation (z1, (z2,loc)) p =
        (case loc of
           Variable l =>
             if hEqual64 z1 z2 then
               if hEqual64 (!l) [] then () 
               else raise Error ("Location not 0 at disposal: "
                                 ^ h2hString (!l), p)
             else raise Error ("Disposed location not of indicated size: "
                               ^ h2hString z1 ^"<>"^ h2hString z2, p)
         | _ =>
             raise Error ("Non-variable location disposed as variable", p))


  fun newarray z vs p =
        ((z, Array (h2int vs, Array.array (h2int vs, [])))
         handle _ =>
           raise Error ("Can not allocate array of size " ^ h2hString vs, p))

  fun disposearray (z1, vs1, (z2, loc)) p =
        (case loc of
           Array (vs2, ve) =>
             if hEqual64 z1 z2 then
               if vs1 = vs2 then
                 if Array.all (hEqual64 []) ve then ()
                 else raise Error ("Array not all 0 at disposal", p)
               else raise Error ("Disposed array not of indicated size", p)
             else raise Error ("Disposed array does not have indicated element size", p)
         | _ => raise Error ("Non-array location disposed as array", p))


  (* rules for l-values *)
  fun do_L eta lval =
    case lval of
      Hermes.Var (x, p) => lookup x eta p (* (Variable/Constant) *)
    | Hermes.Array (x, e, p) => (* (ArrayElement) *)
        let
          val i = do_E eta e
          val j = h2int i
                  handle Overflow => raise Error ("Index far to large", p)
          val (z, vs, ve) =
            case lookup x eta p of
              (z, Array (vs, ve)) => (z, vs, ve)
            | _ => raise Error ("Not an array", p)
        in
          if j < vs then (z, ArrayElement (j, ve))
          else raise Error ("Index out of range: " ^ Int.toString j ^
	                    " in array of size " ^ Int.toString vs, p)
        end
    | Hermes.UnsafeArray (x, e, p) => (* (UnsafeArrayElement) *)
        let
          val i = do_E eta e
          val j = h2int i
                  handle Overflow => raise Error ("Index far to large", p)
          val (z, vs, ve) =
            case lookup x eta p of
              (z, Array (vs, ve)) => (z, vs, ve)
            | _ => raise Error ("Not an array", p)
        in
          if j < vs then (z, ArrayElement (j, ve))
          else raise Error ("Index out of range: " ^ Int.toString j ^
	                    " in array of size " ^ Int.toString vs, p)
        end

  (* evaluate expression *)
  and do_E eta e =
    case e of
      Hermes.Const (c, p) => string2h c p (* (Constant1) *)
    | Hermes.Rval lval =>
        (case do_L eta lval of
           (c, NullLocation) => c  (* (Constant2) *)
         | (z, Variable l) => !l    (* (L-val) *)
         | (z, ArrayElement (j,ve)) => Array.sub (ve, j)
         | (z, Array _) => raise Error ("Array used as variable",(0,0)))
    | Hermes.Un (Hermes.Negate, e1, p) => bNot64 (do_E eta e1) (* (UnOp) *)
    | Hermes.Bin (bop, e1, e2, p) => (* (BinOp) *)
        let
          val v1 = do_E eta e1
          val v2 = do_E eta e2
        in
          case bop of
            Hermes.Plus => hAdd64 v1 v2
          | Hermes.Minus => hSub64 v1 v2
          | Hermes.Times => hTimes64 v1 v2
          | Hermes.Divide => hDiv64 v1 v2 p
          | Hermes.Modulo => hMod64 v1 v2 p
          | Hermes.Xor => hXor64 v1 v2
          | Hermes.BAnd => hAnd64 v1 v2
          | Hermes.BOr => hOr64 v1 v2
          | Hermes.ShiftL => hShiftL64 v1 v2
          | Hermes.ShiftR => hShiftR64 v1 v2
          | Hermes.Equal => if hEqual64 v1 v2 then hMax64 else []
          | Hermes.Less => if hLess64 v1 v2 then hMax64 else []
          | Hermes.Greater => if hGreater64 v1 v2 then hMax64 else []
          | Hermes.Neq => if hEqual64 v1 v2 then [] else hMax64
          | Hermes.Leq => if hLeq64 v1 v2 then hMax64 else []
          | Hermes.Geq => if hGeq64 v1 v2 then hMax64 else []
        end
    | Hermes.Size (x, p) => (* (Size) *)
        (case lookup x eta p of
             (z, Array (vs, ve)) => int2h vs
           | _ => raise Error ("Not an array", p))
    | Hermes.AllZero (x, e, p) =>
        let
          val i = do_E eta e
          val j = h2int i
                  handle Overflow =>
		    raise Error ("Size far to large", p)
          val (z, vs, ve) =
            case lookup x eta p of
              (z, Array (vs, ve)) => (z, vs, ve)
            | _ => raise Error ("Not an array", p)
        in
          if j = vs then
	    if Array.foldl (fn (v,b) => b andalso hEqual64 v []) true ve
	    then hMax64 else []
          else []
        end

   val R = Hermes.R

  (* I function for update operators *)
  fun IUpOp (upOp, z) (v1, v2) p =
    case upOp of
      Hermes.Add => limitZ z (hAdd64 v1 v2)
    | Hermes.Sub => limitZ z (hSub64 v1 v2)
    | Hermes.XorWith => limitZ z (hXor64 v1 v2)
    | Hermes.RoL =>
        let
          val amount = h2int (hMod64 v2 (int2h z) p)
                       (* rotation amount is mod size *)
          val amountL = int2h amount
          val amountR = int2h (z - amount)
        in
          limitZ z (hAdd64 (hShiftL64 v1 amountL) (hShiftR64 v1 amountR))
        end
    | Hermes.RoR =>
        let
          val amount = h2int (hMod64 v2 (int2h z) p)
                       (* rotation amount is mod size *)
          val amountR = int2h amount
          val amountL = int2h (z - amount)
        in
          limitZ z (hAdd64 (hShiftR64 v1 amountR) (hShiftL64 v1 amountL))
        end

  (* makes environment from list of parameters and list of arguments *)
  fun makeEnv eta [] [] = []
    | makeEnv eta (Hermes.VarArg (x, _, _) :: pas) (lv :: ars) =
        (x, do_L eta lv) :: makeEnv eta pas ars
    | makeEnv eta (Hermes.ArrayArg (x, _, _) :: pas) (lv :: ars) =
        (x, do_L eta lv) :: makeEnv eta pas ars
    | makeEnv eta _ _ = raise Error ("Wrong number of args", (0,0))


  (* use declarations to extend environment (and, implicitly, store) *)
  fun do_D eta [] = eta
    | do_D eta (d1 :: ds) =
        let
          val eta1 =
            case d1 of
              Hermes.ConstDecl (x, c, p) =>
                (x, (string2h c p, NullLocation)) :: eta
            | Hermes.VarDecl (x, (_, hz), p) =>
                (case hz of
                   Hermes.U8 => (x, newlocation [8]) :: eta
                 | Hermes.U16 => (x, newlocation [0,1]) :: eta
                 | Hermes.U32 => (x, newlocation [0,2]) :: eta
                 | Hermes.U64 =>  (x, newlocation [0,4]) :: eta)
            | Hermes.ArrayDecl (x, (_, hz), e, p) =>
                 let
                   val vs = do_E eta e
                 in
                   case hz of
                     Hermes.U8 => (x, newarray [8] vs p) :: eta
                   | Hermes.U16 => (x, newarray [0,1] vs p) :: eta
                   | Hermes.U32 => (x, newarray [0,2] vs p) :: eta
                   | Hermes.U64 =>  (x, newarray [0,4] vs p) :: eta
                 end
        in
          do_D eta1 ds
        end


  (* use declarations to check that local variables are zeroed *)
  fun do'inv_D eta [] = eta
    | do'inv_D [] _ =
        raise Error ("Empty environment at undeclaration", (0,0))
                    (* this should not be possible *)
    | do'inv_D ((x, zloc) :: eta) (d1 :: ds) =
        let
          val eta1 = do'inv_D eta ds
        in
          (case d1 of
             Hermes.ConstDecl (y, c, p) => ()
           | Hermes.VarDecl (x, (_, hz), p) =>
               (case hz of
                  Hermes.U8 => disposelocation ([8], zloc) p
                | Hermes.U16 => disposelocation ([0,1], zloc) p
                | Hermes.U32 => disposelocation ([0,2], zloc) p
                | Hermes.U64 => disposelocation ([0,4], zloc) p)
           | Hermes.ArrayDecl (x, (_, hz), e, p) =>
               let
                 val vs = h2int (do_E eta1 e)
               in
                 case hz of
                    Hermes.U8 => disposearray ([8], vs, zloc) p
                  | Hermes.U16 => disposearray ([0,1], vs, zloc) p
                  | Hermes.U32 => disposearray ([0,2], vs, zloc) p
                  | Hermes.U64 => disposearray ([0,4], vs, zloc) p
               end)
          ; eta1
        end

  (* execute statement *)
  fun do_S Delta eta s =
    case s of
      Hermes.Skip => () (* (Empty) *)
      
    | Hermes.Update (upOp, lv, e, p) => (* (Update) *)
        let
          val (z0, loc) = do_L eta lv
          val z = h2int z0
          val v = do_E eta e
        in
          case loc of
            Variable lambda =>
              lambda := IUpOp (upOp, z) (!lambda, limitZ z v) p
          | ArrayElement (i, ve) =>
              Array.update
                (ve, i, IUpOp (upOp, z) (Array.sub (ve, i), limitZ z v) p)
          | _ => raise Error ("Bad location", p)
        end
	
    | Hermes.Swap (lv1, lv2, p) =>
        let
          val (z1, loc1) = do_L eta lv1
          val (z2, loc2) = do_L eta lv2
        in
          case (loc1, loc2) of
            (Variable lambda1, Variable lambda2) =>
               let
                 val t = !lambda1
               in
                 lambda1 := !lambda2;
                 lambda2 := t
               end
          | (Variable lambda1, ArrayElement (i, ve)) =>
               let
                 val t = !lambda1
               in
                 lambda1 := Array.sub (ve, i);
                 Array.update (ve, i, t)
               end
          | (ArrayElement (i, ve), Variable lambda1) =>
               let
                 val t = !lambda1
               in
                 lambda1 := Array.sub (ve, i);
                 Array.update (ve, i, t)
               end
          | (ArrayElement (i1, ve1), ArrayElement (i2, ve2)) =>
               let
                 val t = Array.sub (ve1, i1);
               in
                 Array.update (ve1, i1, Array.sub (ve2, i2));
                 Array.update (ve2, i2, t)
               end
          | _ => raise Error ("Bad location", p)
        end
	
    | Hermes.CondSwap (e, lv1, lv2, p) =>
        if hEqual64 (do_E eta e) [] then ()
        else do_S Delta eta (Hermes.Swap (lv1, lv2, p))
	
    | Hermes.If (e, s1, s2, p) =>
        let
	  val v = do_E eta e
	in
	  if hEqual64 v [] then do_S Delta eta s2
	  else do_S Delta eta s1
	end
	   
    | Hermes.For (x, e1, e2, s, p) =>
        let
          val v1 = do_E eta e1
          val v2 = do_E eta e2
          val refx = ref v1
          val loc = ([0,4], Variable refx)
          val eta1 = (x,loc) :: eta
          fun do_F () =
            if hEqual64 (!refx) v2 then ()
            else
	      (do_S Delta eta1 s;
	       if hEqual64 (!refx) v1 then
	         raise Error ("Loop counter may not return to inititial value", p)
	      else
	        do_F ())
        in
	  do_F ()
        end
	
    | Hermes.Call (f, args, p) =>
        let
          val (pars, s) = lookup f Delta p
          val eta1 = makeEnv eta pars args
        in
          do_S Delta eta1 s
        end
    | Hermes.Uncall (f, args, p) =>
        let
          val (pars, s) = lookup f Delta p
          val eta1 = makeEnv eta pars args
        in
          do_S Delta eta1 (R s)
        end
	
    | Hermes.Block (d, ss, p) =>
        let
          val eta1 = do_D eta d
        in
          List.app (do_S Delta eta1) ss;
          if do'inv_D eta1 (List.rev d) = eta then ()
          else raise Error ("Environment not restored at end of block", p)
        end
	
    | Hermes.Assert (e, p) =>
        if hEqual64 (do_E eta e) []
	then raise Error ("Assertion failed", p)
	else ()

  (* build procedure environment *)
  fun do_P [] = []
    | do_P ((f, pars, s, p) :: ps) = (f, (pars, s)) :: do_P ps

  (* read parameter *)
  fun readPar (Hermes.VarArg (x, (_,hz), p)) =
        let
          val z = case hz of
                    Hermes.U8 => 8
                  | Hermes.U16 => 16
                  | Hermes.U32 => 32
                  | Hermes.U64 => 64
          val str = valOf (TextIO.inputLine TextIO.stdIn)
          val v = limitZ z (string2h str (0,0))
          val loc = (int2h z, Variable (ref v))
        in
          (x, loc)
        end
    | readPar (Hermes.ArrayArg (x, (_,hz), p)) =
        let
          val z = case hz of
                    Hermes.U8 => 8
                  | Hermes.U16 => 16
                  | Hermes.U32 => 32
                  | Hermes.U64 => 64
          val str = valOf (TextIO.inputLine TextIO.stdIn)
          val strs = String.tokens Char.isSpace str
          val ve = List.map (fn st => limitZ z (string2h st (0,0))) strs
          val loc = (int2h z, Array (List.length ve, Array.fromList ve))
        in
          (x, loc)
        end

  (* print parameter *)
  fun printPar eta (Hermes.VarArg (x, (_,hz), p)) =
        let
          val (z, Variable l) = lookup x eta p  (* nonexhaustive *)
        in
          TextIO.print (h2hString (!l) ^ "\n")
        end
    | printPar eta (Hermes.ArrayArg (x, (_,hz), p)) =
        let
          val (z, Array (vs, ve)) = lookup x eta p  (* nonexhaustive *)
        in
          Array.app (fn v => TextIO.print (h2hString v ^ " ")) ve ;
          TextIO.print "\n"
        end

  (* run program by running first procedure *)
  fun run [] backwards = ()
    | run ((f, pars, s, p) :: ps) backwards =
        let
          val Delta = do_P ((f, pars, s, p) :: ps)
          val eta = List.map readPar pars
        in
          (if backwards then do_S Delta eta (R s)
           else  do_S Delta eta s) ;
          List.app (printPar eta) pars
        end

end