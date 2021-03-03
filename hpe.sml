(* Hermes partial evaluator.  Uses assertion reifier *)
(* compile with mosmlc hpe.sml -o hpe *)
structure hpe =
struct

  fun createLexerStream ( is : BasicIO.instream ) =
      Lexing.createLexer ( fn buff => fn n => Nonstdio.buff_input is buff 0 n)

  fun errorMess s = TextIO.output (TextIO.stdErr,s ^ "\n");

  fun hpe filename back =  
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
	     Hermes.showProgram
	       (HermesPE.pe
	          (HermesReify.reifyProgram pgm)
		  back))
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
               | HermesPE.Error (mess, (lin,col)) =>
                     errorMess ("Specialisation error: " ^mess^ " at line "
                      ^ makestring lin ^ ", column " ^ makestring col)
	       | BigInt.BigIntError (mess, (lin,col)) =>
                     errorMess ("Numeric error: " ^mess^ " at line "
                      ^ makestring lin ^ ", column " ^ makestring col)

               | SysErr (s,_) => errorMess ("Exception: " ^ s)
               | Subscript =>  errorMess "subscript error"
      end

  val _ =
    let val cmdLine = Mosml.argv () in
      if List.length cmdLine = 2
      then hpe (List.nth(cmdLine,1)) false
      else if List.length cmdLine = 3 andalso List.nth(cmdLine,1) = "-r"
      then hpe (List.nth(cmdLine,2)) true
      else if List.length cmdLine = 3 andalso List.nth(cmdLine,2) = "-r"
      then hpe (List.nth(cmdLine,1)) true
      else errorMess "call by, e.g., hpe TEA or hpe -r TEA"
    end

(*
  for each public (known) variable, input its value on one line.

  for each secret (unknown) variable, input nothing (no input line)

  for each public array, input its element values on one line,
  separated by spaces.

  for each secret array, input its size on one line.
*)

end
