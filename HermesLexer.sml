local open Obj Lexing in


 open Lexing;

 exception LexicalError of string * (int * int) (* (message, (line, column)) *)

 val currentLine = ref 1
 val lineStartPos = ref [0]

 fun getPos lexbuf = getLineCol (getLexemeStart lexbuf)
				(!currentLine)
				(!lineStartPos)

 and getLineCol pos line (p1::ps) =
       if pos>=p1 then (line, pos-p1)
       else getLineCol pos (line-1) ps
   | getLineCol pos line [] = raise LexicalError ("",(0,0))

 fun lexerError lexbuf s = 
     raise LexicalError (s, getPos lexbuf)

 fun keyword (s, pos) =
     case s of
         "call"         => HermesParser.CALL pos
       | "uncall"       => HermesParser.UNCALL pos
       | "if"           => HermesParser.IF pos
       | "then"         => HermesParser.THEN pos
       | "else"         => HermesParser.ELSE pos
       | "for"          => HermesParser.FOR pos
       | "size"         => HermesParser.SIZE pos
       | "u8"           => HermesParser.U8 pos
       | "u16"          => HermesParser.U16 pos
       | "u32"          => HermesParser.U32 pos
       | "u64"          => HermesParser.U64 pos
       | "const"        => HermesParser.CONST pos
       | "secret"       => HermesParser.SECRET pos
       | "public"       => HermesParser.PUBLIC pos
       | "unsafe"       => HermesParser.UNSAFE pos
       | "assert"       => HermesParser.ASSERT pos
       | "allZero"      => HermesParser.ALLZERO pos
       | _              => HermesParser.ID (s, pos)

 
fun action_44 lexbuf = (
 lexerError lexbuf "Illegal symbol in input" )
and action_43 lexbuf = (
 HermesParser.EOF (getPos lexbuf) )
and action_42 lexbuf = (
 HermesParser.COMMA (getPos lexbuf) )
and action_41 lexbuf = (
 HermesParser.SEMICOLON (getPos lexbuf) )
and action_40 lexbuf = (
 HermesParser.RPAR (getPos lexbuf) )
and action_39 lexbuf = (
 HermesParser.LPAR (getPos lexbuf) )
and action_38 lexbuf = (
 HermesParser.RBRACE (getPos lexbuf) )
and action_37 lexbuf = (
 HermesParser.LBRACE (getPos lexbuf) )
and action_36 lexbuf = (
 HermesParser.RBRACK (getPos lexbuf) )
and action_35 lexbuf = (
 HermesParser.LBRACK (getPos lexbuf) )
and action_34 lexbuf = (
 HermesParser.SWAP (getPos lexbuf) )
and action_33 lexbuf = (
 HermesParser.BNOT (getPos lexbuf) )
and action_32 lexbuf = (
 HermesParser.GEQ (getPos lexbuf) )
and action_31 lexbuf = (
 HermesParser.LEQ (getPos lexbuf) )
and action_30 lexbuf = (
 HermesParser.NEQ (getPos lexbuf) )
and action_29 lexbuf = (
 HermesParser.GREATER (getPos lexbuf) )
and action_28 lexbuf = (
 HermesParser.LESS (getPos lexbuf) )
and action_27 lexbuf = (
 HermesParser.EQUAL (getPos lexbuf) )
and action_26 lexbuf = (
 HermesParser.EQ (getPos lexbuf) )
and action_25 lexbuf = (
 HermesParser.ROR (getPos lexbuf) )
and action_24 lexbuf = (
 HermesParser.ROL (getPos lexbuf) )
and action_23 lexbuf = (
 HermesParser.XORWITH (getPos lexbuf) )
and action_22 lexbuf = (
 HermesParser.SUB (getPos lexbuf) )
and action_21 lexbuf = (
 HermesParser.ADD (getPos lexbuf) )
and action_20 lexbuf = (
 HermesParser.DEC (getPos lexbuf) )
and action_19 lexbuf = (
 HermesParser.INC (getPos lexbuf) )
and action_18 lexbuf = (
 HermesParser.SHIFTR (getPos lexbuf) )
and action_17 lexbuf = (
 HermesParser.SHIFTL (getPos lexbuf) )
and action_16 lexbuf = (
 HermesParser.MASTERSPACE (getPos lexbuf) )
and action_15 lexbuf = (
 HermesParser.BOR (getPos lexbuf) )
and action_14 lexbuf = (
 HermesParser.BAND (getPos lexbuf) )
and action_13 lexbuf = (
 HermesParser.XOR (getPos lexbuf) )
and action_12 lexbuf = (
 HermesParser.MODULO (getPos lexbuf) )
and action_11 lexbuf = (
 HermesParser.DIVIDE (getPos lexbuf) )
and action_10 lexbuf = (
 HermesParser.TIMES (getPos lexbuf) )
and action_9 lexbuf = (
 HermesParser.MINUS (getPos lexbuf) )
and action_8 lexbuf = (
 HermesParser.PLUS (getPos lexbuf) )
and action_7 lexbuf = (
 HermesParser.STRINGCONST
                            (case String.fromCString (getLexeme lexbuf) of
                               NONE => lexerError lexbuf "Bad string constant"
                             | SOME s => String.substring(s,1,
                                                          String.size s - 2),
			    getPos lexbuf) )
and action_6 lexbuf = (
 keyword (getLexeme lexbuf,getPos lexbuf) )
and action_5 lexbuf = (
 HermesParser.NUM (getLexeme lexbuf, getPos lexbuf) )
and action_4 lexbuf = (
 HermesParser.NUM (getLexeme lexbuf, getPos lexbuf) )
and action_3 lexbuf = (
 currentLine := !currentLine+1;
                          lineStartPos :=  getLexemeStart lexbuf
			                   :: !lineStartPos;
                          Token lexbuf )
and action_2 lexbuf = (
 Token lexbuf )
and action_1 lexbuf = (
 Token lexbuf )
and action_0 lexbuf = (
 Token lexbuf )
and state_0 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"A" andalso currChar <= #"Z" then  state_23 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_23 lexbuf
 else if currChar >= #"1" andalso currChar <= #"9" then  state_17 lexbuf
 else case currChar of
    #"\t" => state_3 lexbuf
 |  #"\r" => state_3 lexbuf
 |  #" " => state_3 lexbuf
 |  #"\n" => action_3 lexbuf
 |  #"\f" => action_3 lexbuf
 |  #"~" => action_33 lexbuf
 |  #"}" => action_38 lexbuf
 |  #"|" => action_15 lexbuf
 |  #"{" => action_37 lexbuf
 |  #"^" => state_26 lexbuf
 |  #"]" => action_36 lexbuf
 |  #"[" => action_35 lexbuf
 |  #"@" => action_16 lexbuf
 |  #">" => state_21 lexbuf
 |  #"=" => state_20 lexbuf
 |  #"<" => state_19 lexbuf
 |  #";" => action_41 lexbuf
 |  #"0" => state_16 lexbuf
 |  #"/" => state_15 lexbuf
 |  #"-" => state_14 lexbuf
 |  #"," => action_42 lexbuf
 |  #"+" => state_12 lexbuf
 |  #"*" => action_10 lexbuf
 |  #")" => action_40 lexbuf
 |  #"(" => action_39 lexbuf
 |  #"&" => action_14 lexbuf
 |  #"%" => action_12 lexbuf
 |  #"\"" => state_6 lexbuf
 |  #"!" => state_5 lexbuf
 |  #"\^@" => action_43 lexbuf
 |  _ => action_44 lexbuf
 end)
and state_3 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_0);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\t" => state_57 lexbuf
 |  #"\r" => state_57 lexbuf
 |  #" " => state_57 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_5 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_44);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_30 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_6 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_44);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"(" andalso currChar <= #"[" then  state_53 lexbuf
 else if currChar >= #"]" andalso currChar <= #"~" then  state_53 lexbuf
 else case currChar of
    #"!" => state_53 lexbuf
 |  #" " => state_53 lexbuf
 |  #"&" => state_53 lexbuf
 |  #"%" => state_53 lexbuf
 |  #"$" => state_53 lexbuf
 |  #"#" => state_53 lexbuf
 |  #"\\" => state_55 lexbuf
 |  #"\"" => action_7 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_12 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_8);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_21 lexbuf
 |  #"+" => action_19 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_14 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_9);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_22 lexbuf
 |  #"-" => action_20 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_15 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_11);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"/" => state_46 lexbuf
 |  #"*" => state_45 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_16 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_4);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_42 lexbuf
 else case currChar of
    #"x" => state_43 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_17 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_4);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_42 lexbuf
 else backtrack lexbuf
 end)
and state_19 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_28);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_31 lexbuf
 |  #"<" => state_38 lexbuf
 |  #"-" => state_37 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_20 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_26);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_27 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_21 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_29);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #">" => state_34 lexbuf
 |  #"=" => action_32 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_23 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_32 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_32 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_32 lexbuf
 else case currChar of
    #"_" => state_32 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_26 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_13);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_23 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_32 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_32 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_32 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_32 lexbuf
 else case currChar of
    #"_" => state_32 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_34 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_18);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_25 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_37 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #">" => action_34 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_38 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_17);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_24 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_42 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_4);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_42 lexbuf
 else backtrack lexbuf
 end)
and state_43 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_44 lexbuf
 else if currChar >= #"A" andalso currChar <= #"F" then  state_44 lexbuf
 else if currChar >= #"a" andalso currChar <= #"f" then  state_44 lexbuf
 else backtrack lexbuf
 end)
and state_44 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_5);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_44 lexbuf
 else if currChar >= #"A" andalso currChar <= #"F" then  state_44 lexbuf
 else if currChar >= #"a" andalso currChar <= #"f" then  state_44 lexbuf
 else backtrack lexbuf
 end)
and state_45 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"*" => state_47 lexbuf
 |  #"\^@" => backtrack lexbuf
 |  _ => state_45 lexbuf
 end)
and state_46 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_1);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\^@" => backtrack lexbuf
 |  #"\n" => backtrack lexbuf
 |  _ => state_46 lexbuf
 end)
and state_47 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"/" => action_2 lexbuf
 |  #"\^@" => backtrack lexbuf
 |  _ => state_45 lexbuf
 end)
and state_53 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"(" andalso currChar <= #"[" then  state_53 lexbuf
 else if currChar >= #"]" andalso currChar <= #"~" then  state_53 lexbuf
 else case currChar of
    #"!" => state_53 lexbuf
 |  #" " => state_53 lexbuf
 |  #"&" => state_53 lexbuf
 |  #"%" => state_53 lexbuf
 |  #"$" => state_53 lexbuf
 |  #"#" => state_53 lexbuf
 |  #"\\" => state_55 lexbuf
 |  #"\"" => action_7 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_55 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #" " andalso currChar <= #"~" then  state_53 lexbuf
 else backtrack lexbuf
 end)
and state_57 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_0);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\t" => state_57 lexbuf
 |  #"\r" => state_57 lexbuf
 |  #" " => state_57 lexbuf
 |  _ => backtrack lexbuf
 end)
and Token lexbuf =
  (setLexLastAction lexbuf (magic dummyAction);
   setLexStartPos lexbuf (getLexCurrPos lexbuf);
   state_0 lexbuf)

(* The following checks type consistency of actions *)
val _ = fn _ => [action_44, action_43, action_42, action_41, action_40, action_39, action_38, action_37, action_36, action_35, action_34, action_33, action_32, action_31, action_30, action_29, action_28, action_27, action_26, action_25, action_24, action_23, action_22, action_21, action_20, action_19, action_18, action_17, action_16, action_15, action_14, action_13, action_12, action_11, action_10, action_9, action_8, action_7, action_6, action_5, action_4, action_3, action_2, action_1, action_0];

end
