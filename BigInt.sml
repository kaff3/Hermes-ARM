(* BigInt package for Hermes -- simple but slow *)

structure BigInt =
struct

  (* operations on numbers as lists of hexadecimal digits *)

  exception BigIntError of string*(int*int)

  type hex = int list (* Note: little-endian order *)

  (* hex number to integer.  May overflow *)
  fun h2int [] = 0
    | h2int (h :: hs) = h + 16 * h2int hs

  (* integer to hex number *)
  fun int2h 0 = []
    | int2h n = (n mod 16) :: int2h (n div 16)

  (* limit hex number to 64 bits *)
  fun limit64 hs = if List.length hs > 16 then List.take (hs, 16) else hs

  (* limit hex number to 64 bits *)
  fun limit32 hs = if List.length hs > 8 then List.take (hs, 8) else hs

  (* limit hex number to 16 bits *)
  fun limit16 hs = if List.length hs > 4 then List.take (hs, 4) else hs

  (* limit hex number to 8 bits *)
  fun limit8 hs = if List.length hs > 2 then List.take (hs, 2) else hs

  fun limitZ 8 hs = limit8 hs
    | limitZ 16 hs = limit16 hs
    | limitZ 32 hs = limit32 hs
    | limitZ 64 hs = limit64 hs
    | limitZ z hs =
        raise BigIntError ("Illegal word size " ^ Int.toString z, (0,0))

  (* hex number to hexadecimal string (including 0x) *)
  fun h2hString hs = h2hstring' (List.rev hs)

  and h2hstring' hs =
    if hs = [] then "0x0"
    else if hd hs = 0 then h2hstring' (tl hs)
    else
      "0x" ^
      String.implode
         (List.map
            (fn h => if h <= 9 then Char.chr (h + Char.ord #"0")
                     else Char.chr (h - 10 + Char.ord #"a"))
            hs)

  (* decimal or hexadecimal string to hex number *)
  (* assumes correct number string *)
  fun string2h s p =
    if String.isPrefix " " s then
       string2h (String.extract (s, 1, NONE)) p
    else if String.isSuffix " " s then
      string2h (String.extract (s, 0, SOME (String.size s - 1))) p
    else if String.isSuffix "\n" s then
      string2h (String.extract (s, 0, SOME (String.size s - 1))) p
    else if String.isPrefix "0x" s then (* hexadecimal *)
      limit64
        (List.rev
          (List.map (fn d => if #"0" <= d andalso d <= #"9"
                             then Char.ord d - Char.ord #"0"
                             else if #"a" <= d andalso d <= #"f"
                             then Char.ord d - Char.ord #"a" + 10
                             else Char.ord d - Char.ord #"A" + 10)
                    (String.explode (String.extract (s, 2, NONE)))))
    else (* decimal *)
      ((case Int.fromString s of
          NONE => raise BigIntError ("Bad decimal string " ^ s, p)
        | SOME n => int2h n)
       handle Overflow => raise BigIntError ("decimal string too large", p))
 
  (* binary negation of 64-bit numbers *)
  fun bNot64 hs = if List.length hs < 16 then bNot64 (hs @ [0])
                  else List.map (fn h => 15-h) hs

  (* add with carry *)
  fun hAddC [] hs2 0 = hs2
    | hAddC [] hs2 c = hAddC [c] hs2 0
    | hAddC hs1 [] 0 = hs1
    | hAddC hs1 [] c = hAddC [c] hs1 0
    | hAddC (h1 :: hs1) (h2 :: hs2) c =
        let
          val sum = h1 + h2 + c
        in
          (sum mod 16) :: (hAddC hs1 hs2 (sum div 16))
        end

  (* add and limit to 64 bits *)
  fun hAdd64 hs1 hs2 = limit64 (hAddC hs1 hs2 0)

  (* subtract and limit to 64 bits *)
  fun hSub64 hs1 hs2 =
    limit64 (hAddC hs1 (bNot64 hs2) 1)  (* x-y = x+(not y)+1 *)

  (* binary and of hex digits *)
  fun hAnd4 0 y = 0
    | hAnd4 x 0 = 0
    | hAnd4 x y = (Int.min (x mod 2, y mod 2)) + 2 * hAnd4 (x div 2) (y div 2)

  (* binary or of hex digits *)
  fun hOr4 0 y = y
    | hOr4 x 0 = x
    | hOr4 x y = (Int.max (x mod 2, y mod 2)) + 2 * hOr4 (x div 2) (y div 2)

  (* binary xor of hex digits *)
  fun hXor4 0 y = y
    | hXor4 x 0 = x
    | hXor4 x y = ((x + y) mod 2) + 2 * hXor4 (x div 2) (y div 2)

  (* binary and *)
  fun hAnd64 [] hs2 = []
    | hAnd64 hs1 [] = []
    | hAnd64 (h1 :: hs1) (h2 :: hs2) =
        hAnd4 h1 h2 :: hAnd64 hs1 hs2

  (* binary or *)
  fun hOr64 [] hs2 = hs2
    | hOr64 hs1 [] = hs1
    | hOr64 (h1 :: hs1) (h2 :: hs2) =
        hOr4 h1 h2 :: hOr64 hs1 hs2

  (* binary xor *)
  fun hXor64 [] hs2 = hs2
    | hXor64 hs1 [] = hs1
    | hXor64 (h1 :: hs1) (h2 :: hs2) =
        hXor4 h1 h2 :: hXor64 hs1 hs2

  (* equality *)
  fun hEqual64 [] [] = true
    | hEqual64 [] (h :: hs) = h = 0 andalso hEqual64 [] hs
    | hEqual64 (h :: hs) [] = h = 0 andalso hEqual64 [] hs
    | hEqual64 (h1 :: hs1) (h2 :: hs2) = h1 = h2 andalso hEqual64 hs1 hs2


  (* less than *)
  fun hLess64 hs [] = false
    | hLess64 [] (h :: hs) = h > 0 orelse hLess64 [] hs
    | hLess64 (h1 :: hs1) (h2 :: hs2) =
         hLess64 hs1 hs2 orelse
         h1 < h2 andalso hEqual64 hs1 hs2

  (* greater than *)
  fun hGreater64 hs1 hs2 = hLess64 hs2 hs1

  (* less than or equal to *)
  fun hLeq64 hs1 hs2 = hEqual64 hs1 hs2 orelse hLess64 hs1 hs2

  (* greater than or equal to *)
  fun hGeq64 hs1 hs2 = hLeq64 hs2 hs1

  (* normalise hex number with digits > 15 to have digits <= 15 *)
  fun normalise [] 0 = []
    | normalise [] c = c mod 16 :: normalise [] (c div 16)
    | normalise (h :: hs) c = (h+c) mod 16 :: normalise hs ((h+c) div 16)


  (* shift left *)
  fun hShiftL64 hs1 hs2 = limit64 (hShiftL64' hs1 hs2)

  and hShiftL64' hs1 hs2 =
    if hGeq64 hs2 [0,4] then []
    else if hGeq64 hs2 [4] then 0 :: hShiftL64' hs1 (hSub64 hs2 [4])
    else if hEqual64 hs2 [1] then normalise (List.map (fn h => 2*h) hs1) 0
    else if hEqual64 hs2 [2] then normalise (List.map (fn h => 4*h) hs1) 0
    else if hEqual64 hs2 [3] then normalise (List.map (fn h => 8*h) hs1) 0
    else hs1 (* hs2 = 0 *)

  (* shift right *)
  fun hShiftR64 hs1 hs2 = limit64 (hShiftR64' hs1 hs2)

  and hShiftR64' hs1 hs2 =
    if hGeq64 hs2 (int2h 64) then []
    else if hGeq64 hs2 [4] then
      if null hs1 then [] else hShiftR64' (tl hs1) (hSub64 hs2 [4])
    else if hEqual64 hs2 [] then hs1
    else
      case hShiftL64' hs1 [4 - hd hs2] of
        [] => []
      | (h :: hs) => hs

  (* multiply *)
  fun hTimes64 [] hs2 = []
    | hTimes64 hs1 [] = []
    | hTimes64 (h1 :: hs1) hs2 =
        let
          val x = normalise (List.map (fn h2 => h1*h2) hs2) 0
          val y = 0 :: hTimes64 hs1 hs2
        in
          hAdd64 x y
        end

  fun hDiv64 hs1 hs2 p =
    case (hs1, hs2) of
      (_, []) => raise BigIntError ("Division by 0", p)
    | ([], _) => []
    | (hs1, [2]) => hShiftR64 hs1 [1]
    | (hs1, [4]) => hShiftR64 hs1 [2]
    | (hs1, [8]) => hShiftR64 hs1 [3]
    | (h1 :: hs1, [16]) => hs1
    | (h1 :: hs1, [32]) => hDiv64 hs1 [2] p
    | (h1 :: hs1, [64]) => hDiv64 hs1 [4] p
    | _ =>
          let
            val v1 = (h2int hs1)
                     handle Overflow =>
                       raise BigIntError ("can not divide this big", p)
            val v2 = (h2int hs2)
                     handle Overflow =>
                       raise BigIntError ("can not divide by this big", p)
         in
           int2h (v1 div v2)
         end

  fun hMod64 hs1 hs2 p =
    case (hs1, hs2) of
      (_, []) => raise BigIntError ("Modulo by 0", p)
    | ([], _) => []
    | (h1 :: hs1, [2]) => [h1 mod 2]
    | (h1 :: hs1, [4]) => [h1 mod 4]
    | (h1 :: hs1, [8]) => [h1 mod 8]
    | (h1 :: hs1, [0,1]) => [h1] (* 16 *)
    | ([h1], [0,2]) => [h1] (* 32 *)
    | (h1 :: h2 :: hs1, [0,2]) => [h1, h2 mod 2]
    | ([h1], [0,4]) => [h1] (* 64 *)
    | (h1 :: h2 :: hs1, [0,4]) => [h1, h2 mod 4]
    | _ =>
         let
           val v1 = (h2int hs1)
                    handle Overflow =>
                      raise BigIntError ("can not modulo this big", p)
           val v2 = (h2int hs2)
                    handle Overflow =>
                      raise BigIntError ("can not modulo by this big", p)
         in
           int2h (v1 mod v2)
         end

  val hMax64 = bNot64 []

end