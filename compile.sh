mosmlc -c Hermes.sml
echo "----- Hermes Parser -----"
mosmlyac -v HermesParser.grm
mosmlc -c HermesParser.sig
mosmlc -c HermesParser.sml
echo "----- Hermes Lexer -----"
mosmllex HermesLexer.lex
mosmlc -c HermesLexer.sml
echo "----- Hermes Types -----"
mosmlc -c HermesTypes.sig
mosmlc -c HermesTypes.sml
echo "----- BigInt -----"
mosmlc -c BigInt.sml
echo "----- Hermes Int -----"
mosmlc -c HermesInt.sig
mosmlc -c HermesInt.sml
echo "----- Hermes hi -----"
mosmlc -o bin/hi hi.sml
echo "----- Hermes hr -----"
mosmlc -c HermesReify.sml
mosmlc -o bin/hr hr.sml
echo "----- Hermes PE -----"
mosmlc -c HermesPE.sml
mosmlc -o bin/hpe hpe.sml
echo "----- Hermes cx86 -----"
mosmlc -c x86.sml
mosmlc -c HermesCx64.sml
mosmlc -o bin/hcX64 hcX64.sml

echo "----- Hermes ca64 -----"
mosmlc -c a64.sml
mosmlc -c HermesCa64.sml
mosmlc -o bin/hcA64 hcA64.sml
