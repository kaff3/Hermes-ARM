(* Hermes partial evaluator *)

structure HermesPE =
struct

  open BigInt;;
  
  exception Error of string*(int*int)

  (* lookup in environment *)
  fun lookup x [] pos =
        raise Error ("undeclared identifier" ^ x, pos)
    | lookup x ((y,v) :: env) pos =
        if x = y then v else lookup x env pos

  datatype value = Known of hex
                 | Unknown of Hermes.exp

  (* with variable names and unknown location added *)
  datatype location = Variable of string * value ref
                    | Array of string * int * value array
                    | ArrayElement of string * int * value array
                    | NullLocation
		    | UnknownLoc of Hermes.lVal

  (* Arrays are assumed to have known size *)

  fun liftLoc l p = (* make location into lVal *)
    case l of
      Variable (x,_) => Hermes.Var (x, p)
    | Array (x,_,_) => Hermes.Var (x, p)
    | ArrayElement (x,i,_) =>
        Hermes.Array (x, Hermes.Const (Int.toString i, p), p)
    | NullLocation => raise Error ("Not a real location", p)
    | UnknownLoc lv => lv

  type sizedLocation = hex * location

  (* the store is implicit, so the following functions *)
  (* do not take stores as inputs or outputs *)

  fun newlocation x z = (z, Variable (x, ref (Known [])))

  fun newSecretLocation x z p = (z, UnknownLoc (Hermes.Var (x, p)))
  
  (* takes a position as extra argument for error reporting *)
  fun disposelocation (z1, (z2,loc)) p =
        (case loc of
           Variable (x, l) =>
	     (case !l of
	        Known v =>
                  if hEqual64 z1 z2 then
                    if hEqual64 v [] then () 
                    else raise Error ("Location not 0 at disposal: "
                                      ^ h2hString v, p)
                  else raise Error ("Disposed location not of indicated size: "
                                    ^ h2hString z1 ^"<>"^ h2hString z2, p)
              | Unknown e => ())
	 | UnknownLoc l => ()
         | _ =>
             raise Error ("Non-variable location disposed as variable", p))


  fun newarray x z vs p =
        ((z, Array (x, h2int vs, Array.array (h2int vs, Known [])))
         handle _ =>
           raise Error ("Can not allocate array of size " ^ h2hString vs, p))

  fun newSecretArray x z vs p =
    let
      val es =
        List.tabulate
          (h2int vs,
	   fn i => Unknown
	             (Hermes.Rval
		        (Hermes.Array
			   (x, Hermes.Const (Int.toString i, p), p))))
    in
      ((z, Array (x, h2int vs, Array.fromList es)))
      handle _ =>
        raise Error ("Can not allocate array of size " ^ h2hString vs, p)
    end
    
  fun disposearray (z1, vs1, (z2, loc)) p =
        (case loc of
           Array (x, vs2, ve) =>
             if hEqual64 z1 z2 then
               if vs1 = vs2 then
                 if Array.all (fn (Known h) => hEqual64 [] h | _ => true) ve
		 then ()
                 else raise Error ("Array " ^ x ^ " not all 0 at disposal", p)
               else raise Error ("Disposed array " ^ x ^ " not of indicated size", p)
             else raise Error ("Disposed array " ^ x ^ " does not have indicated element size", p)
	 | UnknownLoc l => ()
         | _ => raise Error ("Non-array location disposed as array", p))


  (* rules for l-values *)
  fun do_L eta lval =
    case lval of
      Hermes.Var (x, p) => lookup x eta p (* (Variable/Constant) *)
    | Hermes.Array (x, e, p) => (* (ArrayElement) *)
        (case do_E eta e of
	   Known i =>
	     let
               val j = h2int i
                       handle Overflow => raise Error ("Index far to large", p)
               val (z, vs, ve) =
                 case lookup x eta p of
                   (z, Array (_, vs, ve)) => (z, vs, ve)
                 | _ => raise Error ("Not an array", p)
             in
               if j < vs then (z, ArrayElement (x, j, ve))
               else raise Error ("Index out of range: " ^ Int.toString j ^
	                         " in array of size " ^ Int.toString vs, p)
             end
	 | Unknown e1 => raise Error ("Array index unknown", p))
    | Hermes.UnsafeArray (x, e, p) => (* (UnsafeArrayElement) *)
        (case (do_E eta e, lookup x eta p) of
	   (Known i, (z, _)) =>
	     (z,
	      UnknownLoc
	        (Hermes.UnsafeArray (x, Hermes.Const (h2hString i, p), p)))
         | (Unknown e1, (z, _)) =>
	     (z, UnknownLoc (Hermes.UnsafeArray (x, e1, p))))
	

  (* evaluate expression *)
  and do_E eta e =
    case e of
      Hermes.Const (c, p) => Known (string2h c p) (* (Constant1) *)
    | Hermes.Rval lval =>
        (case do_L eta lval of
           (c, NullLocation) => Known c  (* (Constant2) *)
         | (z, Variable (_, l)) => !l    (* (L-val) *)
         | (z, ArrayElement (_, j, ve)) => Array.sub (ve, j)
         | (z, Array _) => raise Error ("Array used as variable",(0,0))
	 | (z, UnknownLoc l) => Unknown (Hermes.Rval l))
    | Hermes.Un (Hermes.Negate, e1, p) => (* (UnOp) *)
        (case do_E eta e1 of
	   Known i => Known (bNot64 i)
	 | Unknown e2 => Unknown (Hermes.Un (Hermes.Negate, e2, p)))
    | Hermes.Bin (bop, e1, e2, p) => (* (BinOp) *)
        (case (do_E eta e1, do_E eta e2) of
          (Known v1, Known v2) =>
	    Known
              (case bop of
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
               | Hermes.Geq => if hGeq64 v1 v2 then hMax64 else [])
         | (Known v1, Unknown e2) =>
	      Unknown (Hermes.Bin (bop, Hermes.Const (h2hString v1, p), e2, p))
	 | (Unknown (Hermes.Rval lval), Known v2) =>
	      (case bop of
	         Hermes.Less =>
	           (case do_L eta lval of
  	              (c, NullLocation) =>
		        raise Error ("Constants are known", p)
                    | (z, _) =>
		        (* if lval can not contain v2 or higher *)
		        if hLess64 (limitZ (h2int z) hMax64) v2 then
			  Known hMax64
			else 
	                  Unknown
			    (Hermes.Bin
			       (bop, Hermes.Rval lval,
			       	     Hermes.Const (h2hString v2, p), p)))
               | _ =>
		 Unknown
		   (Hermes.Bin (bop, Hermes.Rval lval,
		    	       	     Hermes.Const (h2hString v2, p), p)))
	 | (Unknown e1, Known v2) =>
	     Unknown (Hermes.Bin (bop, e1, Hermes.Const (h2hString v2, p), p))
	 | (Unknown e1, Unknown e2) =>
	     Unknown (Hermes.Bin (bop, e1, e2, p)))
    | Hermes.Size (x, p) => (* (Size), always known *)
        (case lookup x eta p of
             (z, Array (_, vs, ve)) => Known (int2h vs)
           | _ => raise Error ("Not an array", p))
    | Hermes.AllZero (x, e, p) =>
        (case do_E eta e of
           Known i =>
	     let
               val j = h2int i
                       handle Overflow =>
	                 raise Error ("Size far to large", p)
               val (z, vs, ve) =
                 case lookup x eta p of
                   (z, Array (_, vs, ve)) => (z, vs, ve)
                 | _ => raise Error ("Not an array", p)
             in
               if j = vs then
	         case Array.foldl
		        (fn (Known v, (b,u)) => (b andalso hEqual64 v [],u)
		         | (Unknown _, (b,u)) => (b,true))
		        (true,false) ve
	         of
		   (true, false) => Known hMax64
		 | (false, false) =>  Known []
		 | (_, true) =>
		     Unknown
		       (Hermes.AllZero (x, Hermes.Const (Int.toString j, p), p))
               else Known []
             end
	 | Unknown e1 => raise Error ("Unknown array size", p))


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


  (* use declarations to extend environment (and, implicitly, store)
     and generate residual declarations *)
  fun do_D eta [] = (eta, [])
    | do_D eta (d1 :: ds) =
        let
          val (eta1, ds1) =
            case d1 of
              Hermes.ConstDecl (x, c, p) =>
                ((x, (string2h c p, NullLocation)) :: eta,
		 [])
            | Hermes.VarDecl (x, (Hermes.Public, hz), p) =>
                (case hz of
                   Hermes.U8 => (x, newlocation x [8]) :: eta
                 | Hermes.U16 => (x, newlocation x [0,1]) :: eta
                 | Hermes.U32 => (x, newlocation x [0,2]) :: eta
                 | Hermes.U64 =>  (x, newlocation x [0,4]) :: eta,
		 [])
            | Hermes.VarDecl (x, (Hermes.Secret, hz), p) =>
                (case hz of
                   Hermes.U8 => (x, newSecretLocation x [8] p) :: eta
                 | Hermes.U16 => (x, newSecretLocation x [0,1] p) :: eta
                 | Hermes.U32 => (x, newSecretLocation x [0,2] p) :: eta
                 | Hermes.U64 =>  (x, newSecretLocation x [0,4] p) :: eta,
		 [d1])
            | Hermes.ArrayDecl (x, (Hermes.Public, hz), e, p) =>
                 let
                   val vs = case do_E eta e of
		              Known vs => vs
			    | _ => raise Error ("Unknown size", p)
                 in
                   (case hz of
                      Hermes.U8 => (x, newarray x [8] vs p) :: eta
                    | Hermes.U16 => (x, newarray x [0,1] vs p) :: eta
                    | Hermes.U32 => (x, newarray x [0,2] vs p) :: eta
                    | Hermes.U64 =>  (x, newarray x [0,4] vs p) :: eta,
		    [])
                 end
            | Hermes.ArrayDecl (x, (Hermes.Secret, hz), e, p) =>
                 let
                   val vs = case do_E eta e of
		              Known vs => vs
			    | _ => raise Error ("Unknown size", p)
                 in
                   (case hz of
                      Hermes.U8 => (x, newSecretArray x [8] vs p) :: eta
                    | Hermes.U16 => (x, newSecretArray x [0,1] vs p) :: eta
                    | Hermes.U32 => (x, newSecretArray x [0,2] vs p) :: eta
                    | Hermes.U64 =>  (x, newSecretArray x [0,4] vs p) :: eta,
		    [Hermes.ArrayDecl
		      (x, (Hermes.Secret, hz),
		       Hermes.Const (h2hString vs, p), p)])
                 end
	  val (eta2, ds2) = do_D eta1 ds
        in
	  (eta2, ds1 @ ds2)
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
           | Hermes.VarDecl (x, (Hermes.Public, hz), p) =>
               (case hz of
                  Hermes.U8 => disposelocation ([8], zloc) p
                | Hermes.U16 => disposelocation ([0,1], zloc) p
                | Hermes.U32 => disposelocation ([0,2], zloc) p
                | Hermes.U64 => disposelocation ([0,4], zloc) p)
           | Hermes.VarDecl (x, (Hermes.Secret, hz), p) => ()
           | Hermes.ArrayDecl (x, (Hermes.Public, hz), e, p) =>
               (case do_E eta1 e of
	          Known h =>
	            let
                      val vs = h2int h
                    in
                      case hz of
                         Hermes.U8 => disposearray ([8], vs, zloc) p
                       | Hermes.U16 => disposearray ([0,1], vs, zloc) p
                       | Hermes.U32 => disposearray ([0,2], vs, zloc) p
                       | Hermes.U64 => disposearray ([0,4], vs, zloc) p
                    end
		| Unknown _ => raise Error ("Unknown array size", p))
           | Hermes.ArrayDecl (x, (Hermes.Secret, hz), e, p) => ()
	  )
          ; eta1
        end

  (* execute statement and generate residual statement *)
  fun do_S Delta eta s =
    case s of
      Hermes.Skip => s (* (Empty) *)
      
    | Hermes.Update (upOp, lv, e, p) => (* (Update) *)
        (case (do_L eta lv, do_E eta e) of
           ((z0, loc), Known []) => Hermes.Skip (* no effect *)
         | ((z0, loc), Known v) =>
	     let
               val z = h2int z0
             in
               case loc of
                 Variable (x, lambda) =>
		   (case !lambda of
		      Known w =>
                        (lambda := Known (IUpOp (upOp, z) (w, limitZ z v) p);
                         Hermes.Skip)
		   | Unknown _ =>
                        (lambda := Unknown (Hermes.Rval (Hermes.Var (x,p)));
                         Hermes.Update
			   (upOp, liftLoc loc p,
			    Hermes.Const (h2hString v, p), p)))
               | ArrayElement (x, i, ve) =>
	           (case Array.sub (ve, i) of
		      Known w =>
                        (Array.update
                           (ve, i,
		            Known (IUpOp (upOp, z) (w, limitZ z v) p));
		         Hermes.Skip)
		    | Unknown _ =>
		        (Array.update
			   (ve, i,
			    Unknown
			      (Hermes.Rval
			        (Hermes.Array
			          (x, Hermes.Const (Int.toString i, p), p))));
                         Hermes.Update
			   (upOp, liftLoc loc p,
			    Hermes.Const (h2hString v, p), p)))
               | UnknownLoc l1 =>
	           Hermes.Update (upOp, l1, Hermes.Const (h2hString v, p), p)
               | _ => raise Error ("Bad location", p)
            end
	| ((z0, loc), Unknown e1) =>
	     let
               val z = h2int z0
	       val lv = liftLoc loc p
	       val v1 = Unknown (Hermes.Rval lv)
             in
               (case loc of
                  Variable (x, lambda) => lambda := v1
                | ArrayElement (x, i, ve) => Array.update (ve, i, v1)
                | UnknownLoc l1 => ()
                | _ => raise Error ("Bad location", p)) ;
               Hermes.Update (upOp, lv, e1, p)
            end)
	    
    | Hermes.Swap (lv1, lv2, p) =>
        let
          val (z1, loc1) = do_L eta lv1
          val (z2, loc2) = do_L eta lv2
        in
          case (loc1, loc2) of
            (Variable (x, lambda1), Variable (y, lambda2)) =>
	       (case (!lambda1, !lambda2) of
	          (Known h1, Known h2) =>
                     (lambda1 := Known h2;
                      lambda2 := Known h1;
		      Hermes.Skip)
                | (Unknown lv3, Unknown lv4) =>
		     Hermes.Swap (liftLoc loc1 p, liftLoc loc2 p, p)
                | (_, _) => raise Error ("Bad swap", p))
          | (Variable (x, lambda1), ArrayElement (y, i, ve)) =>
	       (case (!lambda1, Array.sub (ve, i)) of
	          (Known h1, Known h2) =>
                     (lambda1 := Known h2;
                      Array.update (ve, i, Known h1);
	   	      Hermes.Skip)
                | (Unknown lv3, Unknown lv4) =>
		     Hermes.Swap (liftLoc loc1 p, liftLoc loc2 p, p)
                | (_, _) => raise Error ("Bad swap", p))
          | (ArrayElement (x, i, ve), Variable (y, lambda2)) =>
	       (case (Array.sub (ve, i), !lambda2) of
	          (Known h1, Known h2) =>
                     (lambda2 := Known h1;
                      Array.update (ve, i, Known h2);
	   	      Hermes.Skip)
                | (Unknown lv3, Unknown lv4) =>
		     Hermes.Swap (liftLoc loc1 p, liftLoc loc2 p, p)
                | (_, _) => raise Error ("Bad swap", p))
          | (ArrayElement (x, i1, ve1), ArrayElement (y, i2, ve2)) =>
	       (case (Array.sub (ve1, i1), Array.sub (ve2, i2)) of
	          (Known h1, Known h2) =>
                     (Array.update (ve1, i1, Known h2);
                      Array.update (ve2, i2, Known h1);
	   	      Hermes.Skip)
                | (Unknown lv3, Unknown lv4) =>
		     Hermes.Swap (liftLoc loc1 p, liftLoc loc2 p, p)
                | (_, _) => raise Error ("Bad swap", p))
	  | (UnknownLoc l1, loc2) =>
	      Hermes.Swap (l1, liftLoc loc2 p, p)
	  | (loc1, UnknownLoc l2) =>
	      Hermes.Swap (liftLoc loc1 p, l2, p)
          | _ => raise Error ("Bad location", p)
        end
	
    | Hermes.CondSwap (e, lv1, lv2, p) =>
        (case do_E eta e of
	   Known v =>
             if hEqual64 v [] then Hermes.Skip
             else do_S Delta eta (Hermes.Swap (lv1, lv2, p))
	 | Unknown e1 =>
            let
              val (z1, loc1) = do_L eta lv1
              val (z2, loc2) = do_L eta lv2
            in
	      Hermes.CondSwap (e1, liftLoc loc1 p, liftLoc loc2 p, p)
	    end)
	 
    | Hermes.If (e, s1, s2, p) =>
        (case do_E eta e of
	   Known v =>
	     if hEqual64 v [] then do_S Delta eta s2
	     else do_S Delta eta s1
	 | Unknown e => raise Error ("Unknown condition", p))   
	   
    | Hermes.For (x, e1, e2, s, p) =>
        (case (do_E eta e1, do_E eta e2) of
	   (Known v1, Known v2) =>
             let
               val refx = ref (Known v1)
               val loc = ([0,4], Variable (x, refx))
               val eta1 = (x,loc) :: eta
               fun do_F () =
	         (case !refx of
	 	    Known vx =>
                      if hEqual64 vx v2 then []
                      else
		        let
	                  val s1 = (do_S Delta eta1 s)
			  val ss1 =
		            case !refx of
		              Known vx =>
	                        if hEqual64 vx v1 then
	                          raise Error ("Loop counter may not return to inititial value", p)
	                        else
	                          do_F ()
	                   |  Unknown _ =>
			        raise Error ("loop counter has unknown value", p)
			in s1 :: ss1 end
	          | Unknown _ =>
		      raise Error ("loop counter has unknown value", p))
	       val ss1 = List.filter (fn s => s <> Hermes.Skip) (do_F ())
             in
	       HermesReify.makeBlock (ss1, p)
             end
	  | _ => raise Error ("loop bound has unknown value", p))
	  
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
          do_S Delta eta1 (Hermes.R s)
        end
	
    | Hermes.Block (d, ss, p) =>
        let
          val (eta1, d1) = do_D eta d
	  val ss1 = List.filter (fn s => s <> Hermes.Skip)
	                        (List.map (do_S Delta eta1) ss)
        in
          if do'inv_D eta1 (List.rev d) = eta
	  then if ss1 = [] then Hermes.Skip
	       else if d1 = []
	            then HermesReify.makeBlock (ss1, p)
		    else Hermes.Block (d1, ss1, p)
          else raise Error ("Environment not restored at end of block", p)
        end
	
    | Hermes.Assert (e, p) =>
        (case do_E eta e of
	   Known v =>
             if hEqual64 v []
	     then raise Error ("Assertion failed", p)
	     else Hermes.Skip
	 | Unknown e1 => Hermes.Assert (e1, p))


  (* build procedure environment *)
  fun do_P [] = []
    | do_P ((f, pars, s, p) :: ps) = (f, (pars, s)) :: do_P ps

  (* read parameter *)
  fun readPar (Hermes.VarArg (x, (Hermes.Public,hz), p)) =
        let
          val z = case hz of
                    Hermes.U8 => 8
                  | Hermes.U16 => 16
                  | Hermes.U32 => 32
                  | Hermes.U64 => 64
          val str = valOf (TextIO.inputLine TextIO.stdIn)
          val v = Known (limitZ z (string2h str (0,0)))
          val loc = (int2h z, Variable (x, ref v))
        in
          (x, loc)
        end
    | readPar (Hermes.VarArg (x, (Hermes.Secret,hz), p)) =
        let (* read nothing *)
          val z = case hz of
                    Hermes.U8 => 8
                  | Hermes.U16 => 16
                  | Hermes.U32 => 32
                  | Hermes.U64 => 64
          val v = Unknown (Hermes.Rval (Hermes.Var (x, (0,0))))
          val loc = (int2h z, Variable (x, ref v))
        in
          (x, loc)
        end
    | readPar (Hermes.ArrayArg (x, (Hermes.Public,hz), p)) =
        let
          val z = case hz of
                    Hermes.U8 => 8
                  | Hermes.U16 => 16
                  | Hermes.U32 => 32
                  | Hermes.U64 => 64
          val str = valOf (TextIO.inputLine TextIO.stdIn)
          val strs = String.tokens Char.isSpace str
	  val vl = List.length strs
	  val ix = List.tabulate (vl, fn i => i)
	  val ps = ListPair.zip (ix, strs)
          val ve = List.map (fn (i,s) =>
	                       Known (limitZ z (string2h s (0,0))))
		            ps
          val loc = (int2h z, Array (x, vl, Array.fromList ve))
        in
          (x, loc)
        end
    | readPar (Hermes.ArrayArg (x, (Hermes.Secret,hz), p)) =
        let
          val z = case hz of
                    Hermes.U8 => 8
                  | Hermes.U16 => 16
                  | Hermes.U32 => 32
                  | Hermes.U64 => 64
          val str = valOf (TextIO.inputLine TextIO.stdIn)
	  val vl = h2int (string2h str (0,0)) (* read array length *)
	  val ix = List.tabulate (vl, fn i => i)
          val ve = List.map (fn i =>
		                 Unknown
				   (Hermes.Rval
				     (Hermes.Array
				       (x,
				        Hermes.Const (Int.toString i, (0,0)),
					(0,0)))))
		            ix
          val loc = (int2h z, Array (x, vl, Array.fromList ve))
        in
          (x, loc)
        end

  fun isSecret (Hermes.ArrayArg (x, (Hermes.Secret,hz), p)) = true
    | isSecret (Hermes.VarArg (x, (Hermes.Secret,hz), p)) = true
    | isSecret _ = false

  (* specialise program by specialising first procedure *)
  fun pe ((f, pars, s, p) :: ps) false =
        let
          val Delta = do_P ((f, pars, s, p) :: ps)
          val eta = List.map readPar pars
        in
          [(f, List.filter isSecret pars, do_S Delta eta s, p)]
        end
    | pe (p1 :: (f, pars, s, p) :: ps) true =
        (* choose second procedure when running backwards *)
        let
          val Delta = do_P ((f, pars, s, p) :: ps)
          val eta = List.map readPar pars
        in
          [(f, List.filter isSecret pars, do_S Delta eta s, p)]
        end
    | pe _ _ = raise Error ("no procedure to specialise", (0,0))

end