-- Parse occam2.1 code into soccam2.1.
-- vim:et:ts=2

import Data.List
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language (emptyDef)

-- -------------------------------------------------------------

data SExp = Item String | List [SExp]

instance Show SExp where
  show (Item s) = s
  show (List is) = "(" ++ (concat $ intersperse " " $ map show is) ++ ")"

-- -------------------------------------------------------------

occamStyle
    = emptyDef
    { P.commentLine    = "--"
    , P.nestedComments = False
    , P.identStart     = letter
    , P.identLetter    = alphaNum <|> char '.'
    , P.opStart        = oneOf "+-/*"
    , P.reservedOpNames= []
    , P.reservedNames  = ["CHAN", "OF", "BOOL", "BYTE", "INT", "INT16", "INT32", "INT64", "REAL32", "REAL64", "ANY", "FROM", "FOR", "VAL", "IS", "PLACE", "AT", "ALT", "PRI", "SKIP", "CASE", "ROUND", "TRUNC", "MOSTPOS", "MOSTNEG", "SIZE", "BYTESIN", "OFFSETOF", "TRUE", "FALSE", "MINUS", "BITNOT", "NOT", "SIZE", "AFTER"]
    , P.caseSensitive  = True
    }

lexer :: P.TokenParser ()
lexer  = P.makeTokenParser occamStyle

whiteSpace = P.whiteSpace lexer
lexeme    = P.lexeme lexer
symbol    = P.symbol lexer
natural   = P.natural lexer
parens    = P.parens lexer
semi      = P.semi lexer
identifier= P.identifier lexer
reserved  = P.reserved lexer
reservedOp= P.reservedOp lexer

-- XXX these should be operators
sLeft = symbol "["
sRight = symbol "]"
sLeftR = symbol "("
sRightR = symbol ")"
sAssign = symbol ":="
sColon = symbol ":"
sColons = symbol "::"
sComma = symbol ","
sSemi = symbol ";"
sAmp = symbol "&"
sQuest = symbol "?"
sBang = symbol "!"
sEq = symbol "="

sFROM = reserved "FROM"
sFOR = reserved "FOR"
sVAL = reserved "VAL"
sIS = reserved "IS"
sPLACE = reserved "PLACE"
sAT = reserved "AT"
sALT = reserved "ALT"
sPRI = reserved "PRI"
sSKIP = reserved "AT"
sCASE = reserved "CASE"
sROUND = reserved "ROUND"
sTRUNC = reserved "TRUNC"
sMOSTPOS = reserved "MOSTPOS"
sMOSTNEG = reserved "MOSTNEG"
sSIZE = reserved "SIZE"
sBYTESIN = reserved "BYTESIN"
sOFFSETOF = reserved "OFFSETOF"
sTRUE = reserved "TRUE"
sFALSE = reserved "FALSE"
sAFTER = reserved "AFTER"

sIn = symbol "{"
sOut = symbol "}"

-- All of these have type "Parser SExp".

abbreviation
    =   try (do { n <- name ; sIS ; v <- variable ; sColon ; return $ List [Item "is", n, v] })
    <|> try (do { s <- specifier ; n <- name ; sIS ; v <- variable ; sColon ; return $ List [Item "is", s, n, v] })
    <|> try (do { sVAL ; n <- name ; sIS ; v <- variable ; sColon ; return $ List [Item "val-is", n, v] })
    <|> try (do { sVAL ; s <- specifier ; n <- name ; sIS ; v <- variable ; sColon ; return $ List [Item "val-is", s, n, v] })
    <|> try (do { n <- name ; sIS ; v <- channel ; sColon ; return $ List [Item "is", n, v] })
    <|> try (do { s <- specifier ; n <- name ; sIS ; v <- channel ; sColon ; return $ List [Item "is", s, n, v] })
    <|> try (do { n <- name ; sIS ; sLeft ; v <- sepBy1 channel sComma ; sRight ; sColon ; return $ List [Item "is", n, List v] })
    <|> try (do { s <- specifier ; n <- name ; sIS ; sLeft ; v <- sepBy1 channel sComma ; return $ List [Item "is", s, n, List v] })
    <|> try (do { n <- name ; sIS ; v <- timer ; sColon ; return $ List [Item "is", n, v] })
    <|> try (do { s <- specifier ; n <- name ; sIS ; v <- timer ; sColon ; return $ List [Item "is", s, n, v] })
    <|> try (do { n <- name ; sIS ; v <- port ; sColon ; return $ List [Item "is", n, v] })
    <|> do { s <- specifier ; n <- name ; sIS ; v <- port ; sColon ; return $ List [Item "is", s, n, v] }

actual
    =   try variable
    <|> try channel
    <|> try timer
    <|> try port
    <|> expression

allocation
    =   do { sPLACE ; n <- name ; sAT ; e <- expression ; return $ List [Item "place-at", n, e] }

alternation
    =   try (do { sALT ; sIn ; as <- many1 alternative ; sOut ; return $ List ([Item "alt"] ++ as) })
    <|> try (do { sALT ; r <- replicator ; sIn ; a <- alternative ; sOut ; return $ List ([Item "alt", r, a]) })
    <|> try (do { sPRI ; sALT ; sIn ; as <- many1 alternative ; sOut ; return $ List ([Item "pri-alt"] ++ as) })
    <|> do { sPRI ; sALT ; r <- replicator ; sIn ; a <- alternative ; sOut ; return $ List ([Item "pri-alt", r, a]) }

alternative
    =   try guardedAlternative
    <|> try alternation
-- XXX case variants
    <|> do { s <- specification ; a <- alternative ; return $ List [Item ":", s, a] }

assignment
    =   do { vs <- variableList ; sAssign ; es <- expressionList ; return $ List [Item ":=", vs, es] }

base
    =   expression

boolean
    =   expression

byte
    =   do { char '\'' ; c <- character ; char '\'' ; return c }

channel
    =   do { v <- channel' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\ v e -> List [Item "sub", v, e]) v es }

channel'
    =   try name
    <|> try (do { sLeft ; n <- channel ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ List [Item "sub-from-for", n, e, f] })
    <|> try (do { sLeft ; n <- channel ; sFROM ; e <- expression ; sRight ; return $ List [Item "sub-from", n, e] })
    <|> do { sLeft ; n <- channel ; sFOR ; e <- expression ; sRight ; return $ List [Item "sub-for", n, e] }

channelType
    =   try (do { reserved "CHAN" ; reserved "OF" ; p <- protocol ; return $ List [Item "chan-of", p] })
    <|> do { sLeft ; s <- expression ; sRight ; t <- channelType ; return $ List [Item "array", s, t] }

-- XXX wrong
character
    =   do { l <- letter ; return $ Item [l] }

conversion
    =   try (do { t <- dataType ; o <- operand ; return $ List [Item "conv", t, o] })
    <|> try (do { t <- dataType ; sROUND ; o <- operand ; return $ List [Item "round", t, o] })
    <|> do { t <- dataType ; sTRUNC ; o <- operand ; return $ List [Item "trunc", t, o] }

occamCount
    =   expression

dataType
    =   do { try (reserved "BOOL") ; return $ Item "bool" }
    <|> do { try (reserved "BYTE") ; return $ Item "bool" }
    <|> do { try (reserved "INT") ; return $ Item "int" }
    <|> do { try (reserved "INT16") ; return $ Item "int16" }
    <|> do { try (reserved "INT32") ; return $ Item "int32" }
    <|> do { try (reserved "INT64") ; return $ Item "int64" }
    <|> do { try (reserved "REAL32") ; return $ Item "real32" }
    <|> do { try (reserved "REAL64") ; return $ Item "real64" }
    <|> try (do { sLeft ; s <- expression ; sRight ; t <- dataType ; return $ List [Item "array", s, t] })
    <|> name
    <?> "data type"

declaration
    =   try (do { d <- dataType ; n <- name ; sColon ; return $ List [d, n] })
    <|> try (do { d <- channelType ; n <- name ; sColon ; return $ List [d, n] })
    <|> try (do { d <- timerType ; n <- name ; sColon ; return $ List [d, n] })
    <|> try (do { d <- portType ; n <- name ; sColon ; return $ List [d, n] })
    <?> "declaration"

delayedInput
    =   try (do { c <- channel ; sQuest ; sAFTER ; e <- expression ; return $ List [Item "?after", c, e] })

-- NB does not return an SExp
digits
    =   many1 digit

dyadicOperator
    =   try (do { reserved "+" ; return $ Item "+" })
    <|> try (do { reserved "-" ; return $ Item "-" })
    <|> try (do { reserved "*" ; return $ Item "*" })
    <|> try (do { reserved "/" ; return $ Item "/" })
    <|> try (do { reserved "\\" ; return $ Item "mod" })
    <|> try (do { reserved "REM" ; return $ Item "rem" })
    <|> try (do { reserved "PLUS" ; return $ Item "plus" })
    <|> try (do { reserved "MINUS" ; return $ Item "minus" })
    <|> try (do { reserved "TIMES" ; return $ Item "times" })
    <|> try (do { reserved "/\\" ; return $ Item "bitand" })
    <|> try (do { reserved "\\/" ; return $ Item "bitor" })
    <|> try (do { reserved "><" ; return $ Item "bitxor" })
    <|> try (do { reserved "BITAND" ; return $ Item "bitand" })
    <|> try (do { reserved "BITOR" ; return $ Item "bitor" })
    <|> try (do { reserved "AND" ; return $ Item "and" })
    <|> try (do { reserved "OR" ; return $ Item "or" })
    <|> try (do { reserved "=" ; return $ Item "=" })
    <|> try (do { reserved "<>" ; return $ Item "<>" })
    <|> try (do { reserved "<" ; return $ Item "<" })
    <|> try (do { reserved ">" ; return $ Item ">" })
    <|> try (do { reserved ">=" ; return $ Item ">=" })
    <|> try (do { reserved "<=" ; return $ Item "<=" })
    <|> try (do { sAFTER ; return $ Item "after" })

expression
    =   try (do { o <- monadicOperator ; v <- operand ; return $ List [o, v] })
    <|> try (do { a <- operand ; o <- dyadicOperator ; b <- operand ; return $ List [o, a, b] })
    <|> try (do { a <- sMOSTPOS ; t <- dataType ; return $ List [Item "mostpos", t] })
    <|> try (do { a <- sMOSTNEG ; t <- dataType ; return $ List [Item "mostneg", t] })
    <|> try (do { a <- sSIZE ; t <- dataType ; return $ List [Item "size", t] })
    <|> try conversion
    <|> operand

expressionList
    =   try (do { es <- sepBy1 expression sSemi ; return $ List es })
    <|> try (do { n <- name ; sLeftR ; as <- sepBy expression sComma ; sRightR ; return $ List ([Item "call", n] ++ as) })
-- XXX value process

fieldName
    =   name

guard
    =   try input
    <|> try (do { b <- boolean ; sAmp ; i <- input ; return $ List [Item "guarded", b, i] })
    <|> try (do { b <- boolean ; sAmp ; sSKIP ; return $ List [Item "guarded", b, Item "skip"] })

guardedAlternative
    =   do { g <- guard ; sIn ; p <- process ; sOut ; return $ List [g, p] }

hexDigits
    =   do { d <- many1 hexDigit ; return $ Item d }

input
    =   try (do { c <- channel ; sQuest ; is <- sepBy1 inputItem sSemi ; return $ List ([Item "?", c] ++ is) })
    <|> try (do { c <- channel ; sQuest ; sCASE ; tl <- taggedList ; return $ List [Item "?case", c, tl] })
    <|> timerInput
    <|> delayedInput
    <|> do { p <- port ; sQuest ; v <- variable ; return $ List [Item "?", p, v] }

inputItem
    =   try (do { v <- variable ; sColons ; w <- variable ; return $ List [Item "::", v, w] })
    <|> variable

integer
    =   try (do { d <- lexeme digits ; return $ Item d })
    <|> do { char '#' ; d <- lexeme hexDigits ; return $ Item ("#" ++ case d of Item ds -> ds) }

literal
    =   try integer
    <|> try byte
    <|> try real
    <|> try (do { v <- integer ; sLeftR ; t <- dataType ; sRightR ; return $ List [t, v] })
    <|> try (do { v <- byte ; sLeftR ; t <- dataType ; sRightR ; return $ List [t, v] })
    <|> try (do { v <- real ; sLeftR ; t <- dataType ; sRightR ; return $ List [t, v] })
    <|> try (do { sTRUE ; return $ Item "true" })
    <|> do { sFALSE ; return $ Item "false" }

monadicOperator
    =   try (do { reserved "-" ; return $ Item "-" })
    <|> try (do { reserved "MINUS" ; return $ Item "-" })
    <|> try (do { reserved "~" ; return $ Item "bitnot" })
    <|> try (do { reserved "BITNOT" ; return $ Item "bitnot" })
    <|> try (do { reserved "NOT" ; return $ Item "not" })
    <|> do { reserved "SIZE" ; return $ Item "size" }

name
    =   do { s <- identifier ; return $ Item s }

occamString
    =   do { char '"' ; s <- many (noneOf "\"") ; char '"' ; return $ Item ("\"" ++ s ++ "\"") }

operand
    =   do { v <- operand' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\ v e -> List [Item "sub", v, e]) v es }

operand'
    =   try variable
    <|> try literal
    <|> try table
    <|> try (do { sLeftR ; e <- expression ; sRightR ; return e })
-- XXX value process
    <|> try (do { n <- name ; sLeftR ; as <- sepBy expression sComma ; sRightR ; return $ List ([Item "call", n] ++ as) })
    <|> try (do { sBYTESIN ; sLeftR ; o <- operand ; sRightR ; return $ List [Item "bytesin", o] })
    <|> try (do { sBYTESIN ; sLeftR ; o <- dataType ; sRightR ; return $ List [Item "bytesin", o] })
    <|> try (do { sOFFSETOF ; sLeftR ; n <- name ; sComma ; f <- fieldName ; sRightR ; return $ List [Item "offsetof", n, f] })

output
    =   try (do { c <- channel ; sBang ; os <- sepBy1 outputItem sSemi ; return $ List ([Item "!", c] ++ os) })
    <|> try (do { c <- channel ; sBang ; t <- tag ; sSemi ; os <- sepBy1 outputItem sSemi ; return $ List ([Item "!", c, t] ++ os) })
    <|> try (do { c <- channel ; sBang ; t <- tag ; return $ List [Item "!", c, t] })
    <|> do { p <- port ; sBang ; e <- expression ; return $ List [Item "!", p, e] }

outputItem
    =   try (do { a <- expression ; sColons ; b <- expression ; return $ List [Item "::", a, b] })
    <|> expression

port
    =   do { v <- port' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\ v e -> List [Item "sub", v, e]) v es }

port'
    =   try name
    <|> try (do { sLeft ; n <- port ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ List [Item "sub-from-for", n, e, f] })
    <|> try (do { sLeft ; n <- port ; sFROM ; e <- expression ; sRight ; return $ List [Item "sub-from", n, e] })
    <|> do { sLeft ; n <- port ; sFOR ; e <- expression ; sRight ; return $ List [Item "sub-for", n, e] }

portType
    =   try (do { reserved "PORT" ; reserved "OF" ; p <- protocol ; return $ List [Item "port-of", p] })
    <|> do { sLeft ; s <- expression ; sRight ; t <- portType ; return $ List [Item "array", s, t] }

process
    =   try assignment
    <|> try input
    <|> try output
--XXX lots more
    <|> try (do { reserved "SKIP" ; return $ Item "skip" })
    <|> try (do { reserved "STOP" ; return $ Item "stop" })
    <|> try alternation
    <|> try (do { s <- specification ; p <- process ; return $ List [Item ":", s, p] })
    <|> do { a <- allocation ; p <- process ; return $ List [Item ":", a, p] }

protocol
    =   try name
    <|> simpleProtocol

replicator
    =   do { n <- name ; sEq ; b <- base ; sFOR ; c <- occamCount ; return $ List [Item "for", n, b, c] }

sequentialProtocol
    =   do { l <- sepBy1 simpleProtocol sSemi ; return $ List l }

simpleProtocol
    =   try dataType
    <|> try (do { try (reserved "ANY") ; return $ Item "any" })
    <|> do { l <- dataType ; sColons ; r <- dataType ; return $ List [Item "::", l, r] }

specification
    =   try declaration
    <|> try abbreviation
--    <|> definition

specifier
    =   try dataType
    <|> try channelType
    <|> try timerType
    <|> try portType
    <|> try (do { sLeft ; sRight ; s <- specifier ; return $ List [Item "array", s] })
    <|> do { sLeft ; e <- expression ; sRight ; s <- specifier ; return $ List [Item "array", e, s] }

-- XXX (<name> <string>) not (<string> <name>) in case 2 for consistency with literal
table
    =   do { v <- table' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\ v e -> List [Item "sub", v, e]) v es }

table'
    =   try occamString
    <|> try (do { s <- occamString ; sLeftR ; n <- name ; sRightR ; return $ List [n, s] })
    <|> try (do { sLeft ; es <- sepBy1 expression sComma ; sRight ; return $ List es })
    <|> try (do { sLeft ; n <- table ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ List [Item "sub-from-for", n, e, f] })
    <|> try (do { sLeft ; n <- table ; sFROM ; e <- expression ; sRight ; return $ List [Item "sub-from", n, e] })
    <|> try (do { sLeft ; n <- table ; sFOR ; e <- expression ; sRight ; return $ List [Item "sub-for", n, e] })

tag
    =   name

taggedList
    =   try (do { t <- tag ; return $ List [t] })
    <|> do { t <- tag ; sSemi ; is <- sepBy1 inputItem sSemi ; return $ List ([t] ++ is) }

timer
    =   do { v <- timer' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\ v e -> List [Item "sub", v, e]) v es }

timer'
    =   try name
    <|> try (do { sLeft ; n <- timer ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ List [Item "sub-from-for", n, e, f] })
    <|> try (do { sLeft ; n <- timer ; sFROM ; e <- expression ; sRight ; return $ List [Item "sub-from", n, e] })
    <|> do { sLeft ; n <- timer ; sFOR ; e <- expression ; sRight ; return $ List [Item "sub-for", n, e] }

timerInput
    =   try (do { c <- channel ; sQuest ; v <- variable ; return $ List [Item "?", c, v] })

timerType
    =   try (do { reserved "TIMER" ; return $ Item "timer" })
    <|> do { sLeft ; s <- expression ; sRight ; t <- timerType ; return $ List [Item "array", s, t] }

real
    =   try (do { l <- digits ; char '.' ; r <- lexeme digits ; return $ Item (l ++ "." ++ r) })
    <|> do { l <- digits ; char '.' ; r <- digits ; char 'e' ; e <- lexeme digits ; return $ Item (l ++ "." ++ r ++ "e" ++ e) }

variable
    =   do { v <- variable' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\ v e -> List [Item "sub", v, e]) v es }

variable'
    =   try name
    <|> try (do { sLeft ; n <- variable ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ List [Item "sub-from-for", n, e, f] })
    <|> try (do { sLeft ; n <- variable ; sFROM ; e <- expression ; sRight ; return $ List [Item "sub-from", n, e] })
    <|> do { sLeft ; n <- variable ; sFOR ; e <- expression ; sRight ; return $ List [Item "sub-for", n, e] }

variableList
    =   do { vs <- sepBy1 variable sSemi ; return $ List vs }

-- -------------------------------------------------------------

-- XXX this doesn't handle multi-line strings
-- It also discards end-of-lines, but I think that *might* be OK...

countIndent :: String -> Int
countIndent (' ':' ':cs) = 1 + (countIndent cs)
countIndent (' ':cs) = error "Bad indentation"
countIndent _ = 0

stripIndent :: String -> String
stripIndent (' ':cs) = stripIndent cs
stripIndent cs = cs

flatten :: [String] -> String
flatten ls = concat $ intersperse "\n" $ flatten' ls 0
  where
    rep n i = take n (repeat i)
    flatten' [] level = rep level "}"
    flatten' (s:ss) level
      | newLevel > level = (rep (newLevel - level) '{' ++ stripped) : rest
      | newLevel < level = (rep (level - newLevel) '}' ++ stripped) : rest
      | otherwise        = stripped : rest
      where newLevel = countIndent s
            stripped = stripIndent s
            rest = flatten' ss newLevel

-- -------------------------------------------------------------

ex = [
  "INT foo:",
  "[42]CHAN OF [25][9]INT thingy:",
  "ALT",
  "  c ? v",
  "    SKIP",
  "  d ? [x FROM 42 FOR thing + 1]",
  "    STOP",
  "  ALT i = 0 FOR n",
  "    c[i] ? v",
  "      oc ! v"
  ]

flat = putStr $ show $ flatten ex
main = parseTest process $ flatten ex

