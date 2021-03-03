(* Hermes to x86-64 compiler *)
(* Uses partial evaluator, so should be called the same way *)
(* compile with mosmlc hcX64.sml -o hcX64 *)
structure hcX64 =
struct

  fun createLexerStream ( is : BasicIO.instream ) =
      Lexing.createLexer ( fn buff => fn n => Nonstdio.buff_input is buff 0 n)

  fun errorMess s = TextIO.output (TextIO.stdErr,s ^ "\n");

  fun hcX64 filename back withIO =  
      let
        val lexbuf = createLexerStream
			  (BasicIO.open_in (filename ^ ".hms"))
      in
        let
          val pgm = HermesParser.Program HermesLexer.Token lexbuf
	  val _ = HermesTypes.check pgm
	  val reified = HermesReify.reifyProgram pgm
	  val partialled = HermesPE.pe reified back
	  val [(f, args, body, _)] = partialled (* nonexhaustive *)
	  val compiled = HermesCx64.compileProcedure f args body
          val outString =
            "#include <stdio.h>\n" ^
            "#include <stdlib.h>\n" ^
            "#include <inttypes.h>\n" ^
            "#define __STDC_FORMAT_MACROS\n\n" ^
	    
            compiled ^

            (if withIO then
              "int countTokens(char line[])\n{\n" ^
              "  int count = 0, i = 0;\n\n" ^
              "  while (line[i] != '\\n' && line[i] != 0) {\n" ^
              "    while (line[i] == ' ') i++;\n" ^
              "    count++;\n" ^
              "    while (line[i] != ' ' && line[i] != '\\n' && line[i] != 0) i++;\n" ^
              "  }\n" ^
              "  return count;\n" ^
              "}\n\n" ^

              "\n\nint main() {\n" ^
              "  char *line, *c;\n" ^
              "  int i, err;\n" ^
              HermesCx64.declareArgs args ^ "\n" ^
	      "  line = (char *)malloc(2048);\n" ^
              HermesCx64.readArgs args ^
              "  err = " ^ f ^ "(" ^ HermesCx64.callArgs args ^ ");\n\n" ^
	      "  if (err)\n" ^
	      "    printf(\"Assertion failed in line %d col. %d\\n\",\n" ^
	      "           err/10000,err%10000);\n" ^
	      "  else {\n" ^
              HermesCx64.printArgs args ^
              "  \n}\n}\n"
	     else "")
	in
	  TextIO.output (TextIO.stdOut, outString)
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
               | HermesCx64.Error (mess, (lin,col)) =>
                     errorMess ("Compile error: " ^mess^ " at line "
                      ^ makestring lin ^ ", column " ^ makestring col)
               | x86.Error (mess) =>
                     errorMess ("x86 error: " ^ mess)

               | SysErr (s,_) => errorMess ("Exception: " ^ s)
               | Subscript =>  errorMess "subscript error"
      end

  val _ =
    let val cmdLine = Mosml.argv () in
      if List.length cmdLine = 2 (* no flags *)
      then hcX64 (List.nth(cmdLine,1)) false true
      else if List.length cmdLine = 3 andalso List.nth(cmdLine,1) = "-c"
      then hcX64 (List.nth(cmdLine,2)) false false
      else if List.length cmdLine = 3 andalso List.nth(cmdLine,2) = "-c"
      then hcX64 (List.nth(cmdLine,1)) false false
      else if List.length cmdLine = 3 andalso List.nth(cmdLine,1) = "-r"
      then hcX64 (List.nth(cmdLine,2)) true true
      else if List.length cmdLine = 3 andalso List.nth(cmdLine,2) = "-r"
      then hcX64 (List.nth(cmdLine,1)) true true
      else if List.length cmdLine = 3 andalso List.nth(cmdLine,1) = "-cr"
      then hcX64 (List.nth(cmdLine,2)) true false
      else if List.length cmdLine = 3 andalso List.nth(cmdLine,2) = "-cr"
      then hcX64 (List.nth(cmdLine,1)) true false
      else errorMess "call by, e.g., hcX64 TEA,  hxX64 -c TEA, or hxX64 -r TEA"
    end
    
(*
  for each public (known) variable, input its value on one line.

  for each secret (unknown) variable, input nothing (no input line)

  for each public array, input its element values on one line,
  separated by spaces.

  for each secret array, input its size on one line.
*)



end
