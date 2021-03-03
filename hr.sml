(* Hermes assertion reifier *)
(* compile with mosmlc hr.sml -o hr *)
structure hr =
struct

  fun createLexerStream ( is : BasicIO.instream ) =
      Lexing.createLexer ( fn buff => fn n => Nonstdio.buff_input is buff 0 n)

  fun errorMess s = TextIO.output (TextIO.stdErr,s ^ "\n");

  fun hr filename =  
      let
        val lexbuf = createLexerStream
			  (BasicIO.open_in (filename ^ ".hms"))
      in
        let
          val pgm = HermesParser.Program HermesLexer.Token lexbuf
        in
          HermesTypes.check pgm ;
          TextIO.output
	    (TextIO.stdOut,
	     Hermes.showProgram (HermesReify.reifyProgram pgm))
        end
          handle Parsing.yyexit ob => errorMess "Parser-exit\n"
               | Parsing.ParseError ob =>
                   let val (lin,col) = HermesLexer.getPos lexbuf
                   in
                     errorMess ("Parse-error at line "
                      ^ makestring lin ^ ", column " ^ makestring col)
                   end
               | HermesLexer.LexicalError (mess,(lin,col)) =>
                     errorMess ("Lexical error: " ^mess^ " at line "
                      ^ makestring lin ^ ", column " ^ makestring col)
               | HermesTypes.Error (mess, (lin,col)) =>
                     errorMess ("Type error: " ^mess^ " at line "
                      ^ makestring lin ^ ", column " ^ makestring col)
               | SysErr (s,_) => errorMess ("Exception: " ^ s)
               | Subscript =>  errorMess "subscript error"
      end

  val _ =
    let val cmdLine = Mosml.argv () in
      if List.length cmdLine = 2
      then hr (List.nth(cmdLine,1))
      else  errorMess "call by, e.g., hr TEA"
    end

end
