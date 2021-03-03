mosmlc -c Hermes.sml
mosmlyac -v HermesParser.grm
mosmlc -c HermesParser.sig
mosmlc -c HermesParser.sml
mosmllex HermesLexer.lex
mosmlc -c HermesLexer.sml
mosmlc -c HermesTypes.sig
mosmlc -c HermesTypes.sml
mosmlc -c BigInt.sml
mosmlc -c HermesInt.sig
mosmlc -c HermesInt.sml
mosmlc -o bin/hi hi.sml
mosmlc -c HermesReify.sml
mosmlc -o bin/hr hr.sml
mosmlc -c HermesPE.sml
mosmlc -o bin/hpe hpe.sml
mosmlc -c x86.sml
mosmlc -c HermesCx64.sml
mosmlc -o bin/hcX64 hcX64.sml

