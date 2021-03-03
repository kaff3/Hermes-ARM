(* Takes a Hermes program, adds reversed procedures, and reifies checks *)

structure HermesReify =
struct

  fun checkExp e =
    case e of
      Hermes.Const _ => []
    | Hermes.Rval l => checkLval l
    | Hermes.Un (_, e1, _) => checkExp e1
    | Hermes.Bin (_, e1, e2, _) => checkExp e1 @ checkExp e2
    | Hermes.Size _ => []
    | Hermes.AllZero (_, e1, _) => checkExp e1

  and checkLval l =
    case l of
      Hermes.Var _ => []
    | Hermes.Array (x, e, p) =>
        [Hermes.Assert (Hermes.Bin (Hermes.Less, e, Hermes.Size (x, p), p), p)]
    | Hermes.UnsafeArray (x, e, p) =>
        [Hermes.Assert (Hermes.Bin (Hermes.Less, e, Hermes.Size (x, p), p), p)]
	
  fun unBlock [] = []
    | unBlock (Hermes.Block ([], ss1, p) :: ss2) = ss1 @ unBlock ss2
    | unBlock (s :: ss) = s :: unBlock ss
  
  fun makeBlock ([s], p) = s
    | makeBlock (ss, p) =  Hermes.Block ([], unBlock ss, p)

  fun nestedBlock (d, (Hermes.Block (ds, ss1, p1)) :: ss2, p) =
        Hermes.Block (d :: ds, ss1 @ ss2, p)
    | nestedBlock (d, ss, p) =  Hermes.Block ([d], ss, p)
  
  fun reifyStat s =
    case s of
      Hermes.Skip => Hermes.Skip
    | Hermes.Update (uOp, l, e, p) =>
        let
	  val ce = checkExp e
	  val cl = checkLval l
	in
	  makeBlock (ce @ cl @ [s], p)
	end
    | Hermes.Swap (l1, l2, p)  =>
        let
	  val cl1 = checkLval l1
	  val cl2 = checkLval l2
	in
	  makeBlock (cl1 @ cl2 @ [s], p)
	end
    | Hermes.CondSwap (e, l1, l2, p)  =>
        let
	  val ce = checkExp e
	  val cl1 = checkLval l1
	  val cl2 = checkLval l2
	in
	  makeBlock (ce @ cl1 @ cl2 @ [s], p)
	end
    | Hermes.If (e, s1, s2, p) =>
        let
	  val ce = checkExp e
	in
	  makeBlock
	    (ce @ [Hermes.If (e, reifyStat s1, reifyStat s2, p)], p)
	end
    | Hermes.For (x, e1, e2, s1, p) =>
        let
	  val ce1 = checkExp e1
	  val ce2 = checkExp e2
	  val xInit = x ^ "_initial"
	  val xR = Hermes.Rval (Hermes.Var (x, p))
	  val xIL = Hermes.Var (xInit, p)
	  val xIR = Hermes.Rval xIL
	in
	  Hermes.Block
	    ([Hermes.VarDecl (xInit, (Hermes.Public, Hermes.U64),p)],
	     ce1 @ ce2 @
	     [Hermes.Update (Hermes.Add, xIL, e1, p),
	      Hermes.For
		(x, e1, e2,
		 makeBlock
		   ([reifyStat s1,
		     Hermes.Assert (Hermes.Bin (Hermes.Neq, xR, xIR, p),p)],
	            p),
		 p),
	      Hermes.Update (Hermes.Sub, xIL, e1, p)],
	     p)
	end
    | Hermes.Call (f, ls, p) =>
        let
	  val cls = List.concat (List.map checkLval ls)
	in
	  makeBlock (cls @ [Hermes.Call (f ^ "_F", ls, p)], p)
	end
    | Hermes.Uncall (f, ls, p) =>
        let
	  val cls = List.concat (List.map checkLval ls)
	in
	  makeBlock (cls @ [Hermes.Call (f ^ "_B", ls, p)], p)
	end
    | Hermes.Block (ds, ss, p) => reifyBlock ds ss p
    | Hermes.Assert (e, p) =>
        makeBlock (checkExp e @ [s], p)

  and reifyBlock [] ss p =
        makeBlock (List.map reifyStat ss, p)
    | reifyBlock (d :: ds) ss p =
        let
	  val s1 = reifyBlock ds ss p
	in
          case d of
	    Hermes.ConstDecl _ => nestedBlock (d, [s1], p)
          | Hermes.VarDecl (x, vt, p) =>
	      let
	        val xR = Hermes.Rval (Hermes.Var (x, p))
	      in
	        nestedBlock
	          (d,
	           [s1,
	            Hermes.Assert
	              (Hermes.Bin
		         (Hermes.Equal, xR, Hermes.Const ("0", p), p),
		       p)],
	           p)
	      end
          | Hermes.ArrayDecl (x, vt, e, p) =>
	      makeBlock
	        (checkExp e @
	         [nestedBlock
	            (d,
		     [s1, Hermes.Assert (Hermes.AllZero (x, e, p), p)],
		     p)],
	         p)
	end
    
  fun reifyProcedure (f, args, stat, p) =
    [(f ^"_F", args, reifyStat stat, p),
     (f ^ "_B", args, reifyStat (Hermes.R stat), p)]

  fun reifyProgram p = List.concat (List.map reifyProcedure p)
end