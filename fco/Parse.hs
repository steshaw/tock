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
    , P.reservedNames  = ["CHAN", "OF", "BOOL", "BYTE", "INT", "INT16", "INT32", "INT64", "REAL32", "REAL64", "ANY", "FROM", "FOR", "VAL", "IS", "PLACE", "AT", "ALT", "PRI", "SKIP", "STOP", "CASE", "ROUND", "TRUNC", "MOSTPOS", "MOSTNEG", "SIZE", "BYTESIN", "OFFSETOF", "TRUE", "FALSE", "MINUS", "BITNOT", "NOT", "SIZE", "AFTER", "DATA", "TYPE", "PROTOCOL", "PROC", "RETYPES", "RESHAPES", "FUNCTION", "VALOF", "RESULT", "RECORD", "PACKED"]
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
sSKIP = reserved "SKIP"
sSTOP = reserved "STOP"
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
sDATA = reserved "DATA"
sTYPE = reserved "TYPE"
sPROTOCOL = reserved "PROTOCOL"
sPROC = reserved "PROC"
sRETYPES = reserved "RETYPES"
sRESHAPES = reserved "RESHAPES"
sFUNCTION = reserved "FUNCTION"
sVALOF = reserved "VALOF"
sRESULT = reserved "RESULT"
sRECORD = reserved "RECORD"
sPACKED = reserved "PACKED"

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
    <?> "abbreviation"

actual
    =   try variable
    <|> try channel
    <|> try timer
    <|> try port
    <|> expression
    <?> "actual"

allocation
    =   do { sPLACE ; n <- name ; sAT ; e <- expression ; return $ List [Item "place-at", n, e] }
    <?> "allocation"

alternation
    =   try (do { sALT ; sIn ; as <- many1 alternative ; sOut ; return $ List ([Item "alt"] ++ as) })
    <|> try (do { sALT ; r <- replicator ; sIn ; a <- alternative ; sOut ; return $ List ([Item "alt", r, a]) })
    <|> try (do { sPRI ; sALT ; sIn ; as <- many1 alternative ; sOut ; return $ List ([Item "pri-alt"] ++ as) })
    <|> do { sPRI ; sALT ; r <- replicator ; sIn ; a <- alternative ; sOut ; return $ List ([Item "pri-alt", r, a]) }
    <?> "alternation"

alternative
    =   try guardedAlternative
    <|> try alternation
    <|> try (do { c <- channel ; sQuest ; sCASE ; sIn ; vs <- many1 variant ; sOut ; return $ List ([Item "?case", c] ++ vs) })
    <|> try (do { b <- boolean ; sAmp ; c <- channel ; sQuest ; sCASE ; sIn ; vs <- many1 variant ; sOut ; return $ List ([Item "?case-guarded", b, c] ++ vs) })
    <|> do { s <- specification ; a <- alternative ; return $ List [Item ":", s, a] }
    <?> "alternative"

assignment
    =   do { vs <- variableList ; sAssign ; es <- expressionList ; return $ List [Item ":=", vs, es] }
    <?> "assignment"

base
    =   expression
    <?> "base"

boolean
    =   expression
    <?> "boolean"

byte
    =   do { char '\'' ; c <- character ; char '\'' ; return c }
    <?> "byte"

channel
    =   do { v <- channel' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\ v e -> List [Item "sub", v, e]) v es }
    <?> "channel"

channel'
    =   try name
    <|> try (do { sLeft ; n <- channel ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ List [Item "sub-from-for", n, e, f] })
    <|> try (do { sLeft ; n <- channel ; sFROM ; e <- expression ; sRight ; return $ List [Item "sub-from", n, e] })
    <|> do { sLeft ; n <- channel ; sFOR ; e <- expression ; sRight ; return $ List [Item "sub-for", n, e] }
    <?> "channel'"

channelType
    =   try (do { reserved "CHAN" ; reserved "OF" ; p <- protocol ; return $ List [Item "chan-of", p] })
    <|> do { sLeft ; s <- expression ; sRight ; t <- channelType ; return $ List [Item "array", s, t] }
    <?> "channelType"

-- XXX wrong
character
    =   do { l <- letter ; return $ Item [l] }
    <?> "character"

conversion
    =   try (do { t <- dataType ; o <- operand ; return $ List [Item "conv", t, o] })
    <|> try (do { t <- dataType ; sROUND ; o <- operand ; return $ List [Item "round", t, o] })
    <|> do { t <- dataType ; sTRUNC ; o <- operand ; return $ List [Item "trunc", t, o] }
    <?> "conversion"

occamCount
    =   expression
    <?> "count"

dataType
    =   do { try (reserved "BOOL") ; return $ Item "bool" }
    <|> do { try (reserved "BYTE") ; return $ Item "byte" }
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

definition
    =   try (do { sDATA ; sTYPE ; n <- name ; sIS ; t <- dataType ; sColon ; return $ List [Item "data-type", n, t] })
    <|> try (do { sDATA ; sTYPE ; n <- name ; sIn ; t <- structuredType ; sOut ; sColon ; return $ List [Item "data-type", n, t] })
    <|> try (do { sPROTOCOL ; n <- name ; sIS ; p <- simpleProtocol ; sColon ; return $ List [Item "protocol", n, p] })
    <|> try (do { sPROTOCOL ; n <- name ; sIS ; p <- sequentialProtocol ; sColon ; return $ List [Item "protocol", n, p] })
    <|> try (do { sPROTOCOL ; n <- name ; sIn ; sCASE ; sIn ; ps <- many1 taggedProtocol ; sOut ; sOut ; sColon ; return $ List [Item "protocol", n, List ps] })
    <|> try (do { sPROC ; n <- name ; fs <- formalList ; sIn ; p <- process ; sOut ; sColon ; return $ List [Item "proc", n, fs, p] })
    <|> try (do { rs <- sepBy1 dataType sComma ; (n, fs) <- functionHeader ; sIn ; vp <- valueProcess ; sOut ; sColon ; return $ List [Item "fun", List rs, n, fs, vp] })
    <|> try (do { rs <- sepBy1 dataType sComma ; (n, fs) <- functionHeader ; sIS ; el <- expressionList ; sColon ; return $ List [Item "fun-is", List rs, n, fs, el] })
    <|> try (do { s <- specifier ; n <- name ; sRETYPES ; v <- variable ; sColon ; return $ List [Item "retypes", s, n, v] })
    <|> try (do { sVAL ; s <- specifier ; n <- name ; sRETYPES ; v <- variable ; sColon ; return $ List [Item "val-retypes", s, n, v] })
    <|> try (do { s <- specifier ; n <- name ; sRETYPES ; v <- channel ; sColon ; return $ List [Item "retypes", s, n, v] })
    <|> try (do { s <- specifier ; n <- name ; sRETYPES ; v <- port ; sColon ; return $ List [Item "retypes", s, n, v] })
    <|> try (do { s <- specifier ; n <- name ; sRESHAPES ; v <- variable ; sColon ; return $ List [Item "reshapes", s, n, v] })
    <|> try (do { sVAL ; s <- specifier ; n <- name ; sRESHAPES ; v <- variable ; sColon ; return $ List [Item "val-reshapes", s, n, v] })
    <|> try (do { s <- specifier ; n <- name ; sRESHAPES ; v <- channel ; sColon ; return $ List [Item "reshapes", s, n, v] })
    <|> do { s <- specifier ; n <- name ; sRESHAPES ; v <- port ; sColon ; return $ List [Item "reshapes", s, n, v] }
    <?> "definition"

delayedInput
    =   try (do { c <- channel ; sQuest ; sAFTER ; e <- expression ; return $ List [Item "?after", c, e] })
    <?> "delayedInput"

-- NB does not return an SExp
digits
    =   many1 digit
    <?> "digits"

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
    <?> "dyadicOperator"

occamExponent
    =   try (do { c <- oneOf "+-" ; d <- digits ; return $ c : d })

expression
    =   try (do { o <- monadicOperator ; v <- operand ; return $ List [o, v] })
    <|> try (do { a <- operand ; o <- dyadicOperator ; b <- operand ; return $ List [o, a, b] })
    <|> try (do { a <- sMOSTPOS ; t <- dataType ; return $ List [Item "mostpos", t] })
    <|> try (do { a <- sMOSTNEG ; t <- dataType ; return $ List [Item "mostneg", t] })
    <|> try (do { a <- sSIZE ; t <- dataType ; return $ List [Item "size", t] })
    <|> try conversion
    <|> operand
    <?> "expression"

expressionList
    =   try (do { es <- sepBy1 expression sComma ; return $ List es })
    <|> try (do { n <- name ; sLeftR ; as <- sepBy expression sComma ; sRightR ; return $ List ([Item "call", n] ++ as) })
-- XXX value process
    <?> "expressionList"

fieldName
    =   name
    <?> "fieldName"

-- This is rather different from the grammar.
formalList
    =   do { sLeftR ; fs <- sepBy formalArg sComma ; sRightR ; return $ List (map List (reverse (reduce (reverse fs) []))) }
    where
      formalArg :: Parser ([[SExp]] -> [[SExp]])
      formalArg =   try (do { sVAL ; s <- specifier ; n <- name ; return $ addToList [Item "val", s] n })
                <|> try (do { s <- specifier ; n <- name ; return $ addToList [s] n })
                <|> try (do { n <- name ; return $ addToList [] n })

      addToList :: [SExp] -> SExp -> [[SExp]] -> [[SExp]]
      addToList [] n (l:ls) = (l ++ [n]) : ls
      addToList s n ls = (s ++ [n]) : ls

      reduce [] x = x
      reduce (f:fs) x = f (reduce fs x)

functionHeader
    =   do { sFUNCTION ; n <- name ; fs <- formalList ; return $ (n, fs) }

guard
    =   try input
    <|> try (do { b <- boolean ; sAmp ; i <- input ; return $ List [Item "guarded", b, i] })
    <|> try (do { b <- boolean ; sAmp ; sSKIP ; return $ List [Item "guarded", b, Item "skip"] })
    <?> "guard"

guardedAlternative
    =   do { g <- guard ; sIn ; p <- process ; sOut ; return $ List [g, p] }
    <?> "guardedAlternative"

hexDigits
    =   do { d <- many1 hexDigit ; return $ Item d }
    <?> "hexDigits"

input
    =   try (do { c <- channel ; sQuest ; is <- sepBy1 inputItem sSemi ; return $ List ([Item "?", c] ++ is) })
    <|> try (do { c <- channel ; sQuest ; sCASE ; tl <- taggedList ; return $ List [Item "?case", c, tl] })
    <|> timerInput
    <|> delayedInput
    <|> do { p <- port ; sQuest ; v <- variable ; return $ List [Item "?", p, v] }
    <?> "input"

inputItem
    =   try (do { v <- variable ; sColons ; w <- variable ; return $ List [Item "::", v, w] })
    <|> variable
    <?> "inputItem"

integer
    =   try (do { d <- lexeme digits ; return $ Item d })
    <|> do { char '#' ; d <- lexeme hexDigits ; return $ Item ("#" ++ case d of Item ds -> ds) }
    <?> "integer"

literal
    =   try real
    <|> try integer
    <|> try byte
    <|> try (do { v <- real ; sLeftR ; t <- dataType ; sRightR ; return $ List [t, v] })
    <|> try (do { v <- integer ; sLeftR ; t <- dataType ; sRightR ; return $ List [t, v] })
    <|> try (do { v <- byte ; sLeftR ; t <- dataType ; sRightR ; return $ List [t, v] })
    <|> try (do { sTRUE ; return $ Item "true" })
    <|> do { sFALSE ; return $ Item "false" }
    <?> "literal"

monadicOperator
    =   try (do { reserved "-" ; return $ Item "-" })
    <|> try (do { reserved "MINUS" ; return $ Item "-" })
    <|> try (do { reserved "~" ; return $ Item "bitnot" })
    <|> try (do { reserved "BITNOT" ; return $ Item "bitnot" })
    <|> try (do { reserved "NOT" ; return $ Item "not" })
    <|> do { reserved "SIZE" ; return $ Item "size" }
    <?> "monadicOperator"

name
    =   do { s <- identifier ; return $ Item s }
    <?> "name"

occamString
    =   do { char '"' ; s <- many (noneOf "\"") ; char '"' ; return $ Item ("\"" ++ s ++ "\"") }
    <?> "string"

operand
    =   do { v <- operand' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\ v e -> List [Item "sub", v, e]) v es }
    <?> "operand"

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
    <?> "operand'"

output
    =   try (do { c <- channel ; sBang ; os <- sepBy1 outputItem sSemi ; return $ List ([Item "!", c] ++ os) })
    <|> try (do { c <- channel ; sBang ; t <- tag ; sSemi ; os <- sepBy1 outputItem sSemi ; return $ List ([Item "!", c, t] ++ os) })
    <|> try (do { c <- channel ; sBang ; t <- tag ; return $ List [Item "!", c, t] })
    <|> do { p <- port ; sBang ; e <- expression ; return $ List [Item "!", p, e] }
    <?> "output"

outputItem
    =   try (do { a <- expression ; sColons ; b <- expression ; return $ List [Item "::", a, b] })
    <|> expression
    <?> "outputItem"

port
    =   do { v <- port' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\ v e -> List [Item "sub", v, e]) v es }
    <?> "port"

port'
    =   try name
    <|> try (do { sLeft ; n <- port ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ List [Item "sub-from-for", n, e, f] })
    <|> try (do { sLeft ; n <- port ; sFROM ; e <- expression ; sRight ; return $ List [Item "sub-from", n, e] })
    <|> do { sLeft ; n <- port ; sFOR ; e <- expression ; sRight ; return $ List [Item "sub-for", n, e] }
    <?> "port'"

portType
    =   try (do { reserved "PORT" ; reserved "OF" ; p <- protocol ; return $ List [Item "port-of", p] })
    <|> do { sLeft ; s <- expression ; sRight ; t <- portType ; return $ List [Item "array", s, t] }
    <?> "portType"

process
    =   try assignment
    <|> try input
    <|> try output
--XXX lots more
    <|> try (do { sSKIP ; return $ Item "skip" })
    <|> try (do { sSTOP ; return $ Item "stop" })
    <|> try alternation
    <|> try (do { s <- specification ; p <- process ; return $ List [Item ":", s, p] })
    <|> do { a <- allocation ; p <- process ; return $ List [Item ":", a, p] }
    <?> "process"

protocol
    =   try name
    <|> simpleProtocol
    <?> "protocol"

real
    =   try (do { l <- digits ; char '.' ; r <- digits ; char 'e' ; e <- lexeme occamExponent ; return $ Item (l ++ "." ++ r ++ "e" ++ e) })
    <|> do { l <- digits ; char '.' ; r <- lexeme digits ; return $ Item (l ++ "." ++ r) }
    <?> "real"

replicator
    =   do { n <- name ; sEq ; b <- base ; sFOR ; c <- occamCount ; return $ List [Item "for", n, b, c] }
    <?> "replicator"

sequentialProtocol
    =   do { l <- sepBy1 simpleProtocol sSemi ; return $ List l }
    <?> "sequentialProtocol"

simpleProtocol
    =   try dataType
    <|> try (do { try (reserved "ANY") ; return $ Item "any" })
    <|> do { l <- dataType ; sColons ; r <- dataType ; return $ List [Item "::", l, r] }
    <?> "simpleProtocol"

specification
    =   try declaration
    <|> try abbreviation
    <|> definition
    <?> "specification"

specifier
    =   try dataType
    <|> try channelType
    <|> try timerType
    <|> try portType
    <|> try (do { sLeft ; sRight ; s <- specifier ; return $ List [Item "array", s] })
    <|> do { sLeft ; e <- expression ; sRight ; s <- specifier ; return $ List [Item "array", e, s] }
    <?> "specifier"

structuredType
    =   try (do { sRECORD ; sIn ; fs <- many1 structuredTypeField ; sOut ; return $ List ([Item "record"] ++ fs) })
    <|> do { sPACKED ; sRECORD ; sIn ; fs <- many1 structuredTypeField ; sOut ; return $ List ([Item "packed-record"] ++ fs) }

structuredTypeField
    =   do { t <- dataType ; fs <- many1 fieldName ; sColon ; return $ List (t : fs) }

-- XXX (<name> <string>) not (<string> <name>) in case 2 for consistency with literal
table
    =   do { v <- table' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\ v e -> List [Item "sub", v, e]) v es }
    <?> "table"

table'
    =   try occamString
    <|> try (do { s <- occamString ; sLeftR ; n <- name ; sRightR ; return $ List [n, s] })
    <|> try (do { sLeft ; es <- sepBy1 expression sComma ; sRight ; return $ List es })
    <|> try (do { sLeft ; n <- table ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ List [Item "sub-from-for", n, e, f] })
    <|> try (do { sLeft ; n <- table ; sFROM ; e <- expression ; sRight ; return $ List [Item "sub-from", n, e] })
    <|> try (do { sLeft ; n <- table ; sFOR ; e <- expression ; sRight ; return $ List [Item "sub-for", n, e] })
    <?> "table'"

tag
    =   name
    <?> "tag"

taggedList
    =   try (do { t <- tag ; sSemi ; is <- sepBy1 inputItem sSemi ; return $ List ([t] ++ is) })
    <|> do { t <- tag ; return $ List [t] }
    <?> "taggedList"

taggedProtocol
    =   try (do { t <- tag ; return $ List [t] })
    <|> try (do { t <- tag ; sp <- sequentialProtocol ; return $ List (t : case sp of List ps -> ps) })

timer
    =   do { v <- timer' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\ v e -> List [Item "sub", v, e]) v es }
    <?> "timer"

timer'
    =   try name
    <|> try (do { sLeft ; n <- timer ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ List [Item "sub-from-for", n, e, f] })
    <|> try (do { sLeft ; n <- timer ; sFROM ; e <- expression ; sRight ; return $ List [Item "sub-from", n, e] })
    <|> do { sLeft ; n <- timer ; sFOR ; e <- expression ; sRight ; return $ List [Item "sub-for", n, e] }
    <?> "timer'"

timerInput
    =   try (do { c <- channel ; sQuest ; v <- variable ; return $ List [Item "?", c, v] })
    <?> "timerInput"

timerType
    =   try (do { reserved "TIMER" ; return $ Item "timer" })
    <|> do { sLeft ; s <- expression ; sRight ; t <- timerType ; return $ List [Item "array", s, t] }
    <?> "timerType"

valueProcess
    =   try (do { sVALOF ; sIn ; p <- process ; sRESULT ; el <- expressionList ; sOut ; return $ List [Item "valof", p, el] })
    <|> do { s <- specification ; v <- valueProcess ; return $ List [Item ":", s, v] }

variable
    =   do { v <- variable' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\ v e -> List [Item "sub", v, e]) v es }
    <?> "variable"

variable'
    =   try name
    <|> try (do { sLeft ; n <- variable ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ List [Item "sub-from-for", n, e, f] })
    <|> try (do { sLeft ; n <- variable ; sFROM ; e <- expression ; sRight ; return $ List [Item "sub-from", n, e] })
    <|> do { sLeft ; n <- variable ; sFOR ; e <- expression ; sRight ; return $ List [Item "sub-for", n, e] }
    <?> "variable'"

variableList
    =   do { vs <- sepBy1 variable sComma ; return $ List vs }
    <?> "variableList"

variant
    =   try (do { t <- taggedList ; sIn ; p <- process ; sOut ; return $ List [t, p] })
    <|> do { s <- specification ; v <- variant ; return $ List [Item ":", s, v] }
    <?> "variant"

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
  "      oc ! v",
  "  tc ? CASE",
  "    One",
  "      SKIP",
  "    BOOL b:",
  "    Two ; b",
  "      SKIP"
  ]

flat = putStr $ show $ flatten ex
main = parseTest process $ flatten ex

