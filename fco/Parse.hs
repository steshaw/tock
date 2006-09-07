-- Parse occam code

module Parse (parseSourceFile, prepare) where

import Data.List
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language (emptyDef)
import qualified IO

import Tree

-- -------------------------------------------------------------

mainMarker = "##MAGIC-FCO-MAIN-PROCESS##"

occamStyle
    = emptyDef
    { P.commentLine    = "--"
    , P.nestedComments = False
    , P.identStart     = letter
    , P.identLetter    = alphaNum <|> char '.'
    , P.opStart        = oneOf "+-*/\\>=<~"
    , P.opLetter       = oneOf "/\\>=<"
    , P.reservedOpNames= [
                          "+",
                          "-",
                          "*",
                          "/",
                          "\\",
                          "/\\",
                          "\\/",
                          "><",
                          "=",
                          "<>",
                          "<",
                          ">",
                          ">=",
                          "<=",
                          "-",
                          "~"
                         ]
    , P.reservedNames  = [
                          "AFTER",
                          "ALT",
                          "AND",
                          "ANY",
                          "AT",
                          "BITAND",
                          "BITNOT",
                          "BITOR",
                          "BOOL",
                          "BYTE",
                          "BYTESIN",
                          "CASE",
                          "CHAN",
                          "DATA",
                          "ELSE",
                          "FALSE",
                          "FOR",
                          "FROM",
                          "FUNCTION",
                          "IF",
                          "INT",
                          "INT16",
                          "INT32",
                          "INT64",
                          "IS",
                          "MINUS",
                          "MOSTNEG",
                          "MOSTPOS",
                          "NOT",
                          "OF",
                          "OFFSETOF",
                          "OR",
                          "PACKED",
                          "PAR",
                          "PLACE",
                          "PLACED",
                          "PLUS",
                          "PORT",
                          "PRI",
                          "PROC",
                          "PROCESSOR",
                          "PROTOCOL",
                          "REAL32",
                          "REAL64",
                          "RECORD",
                          "REM",
                          "RESHAPES",
                          "RESULT",
                          "RETYPES",
                          "ROUND",
                          "SEQ",
                          "SIZE",
                          "SKIP",
                          "STOP",
                          "TIMER",
                          "TIMES",
                          "TRUE",
                          "TRUNC",
                          "TYPE",
                          "VAL",
                          "VALOF",
                          "WHILE",
                          mainMarker
                         ]
    , P.caseSensitive  = True
    }

lexer :: P.TokenParser ()
lexer  = P.makeTokenParser occamStyle
-- XXX replace whitespace with something that doesn't eat \ns

whiteSpace = P.whiteSpace lexer
lexeme    = P.lexeme lexer
symbol    = P.symbol lexer
natural   = P.natural lexer
parens    = P.parens lexer
semi      = P.semi lexer
identifier= P.identifier lexer
reserved  = P.reserved lexer
reservedOp= P.reservedOp lexer

sLeft = try $ symbol "["
sRight = try $ symbol "]"
sLeftR = try $ symbol "("
sRightR = try $ symbol ")"
sAssign = try $ symbol ":="
sColon = try $ symbol ":"
sColons = try $ symbol "::"
sComma = try $ symbol ","
sSemi = try $ symbol ";"
sAmp = try $ symbol "&"
sQuest = try $ symbol "?"
sBang = try $ symbol "!"
sEq = try $ symbol "="

sAFTER = reserved "AFTER"
sALT = reserved "ALT"
sAND = reserved "AND"
sANY = reserved "ANY"
sAT = reserved "AT"
sBITAND = reserved "BITAND"
sBITNOT = reserved "BITNOT"
sBITOR = reserved "BITOR"
sBOOL = reserved "BOOL"
sBYTE = reserved "BYTE"
sBYTESIN = reserved "BYTESIN"
sCASE = reserved "CASE"
sCHAN = reserved "CHAN"
sDATA = reserved "DATA"
sELSE = reserved "ELSE"
sFALSE = reserved "FALSE"
sFOR = reserved "FOR"
sFROM = reserved "FROM"
sFUNCTION = reserved "FUNCTION"
sIF = reserved "IF"
sINT = reserved "INT"
sINT16 = reserved "INT16"
sINT32 = reserved "INT32"
sINT64 = reserved "INT64"
sIS = reserved "IS"
sMINUS = reserved "MINUS"
sMOSTNEG = reserved "MOSTNEG"
sMOSTPOS = reserved "MOSTPOS"
sNOT = reserved "NOT"
sOF = reserved "OF"
sOFFSETOF = reserved "OFFSETOF"
sOR = reserved "OR"
sPACKED = reserved "PACKED"
sPAR = reserved "PAR"
sPLACE = reserved "PLACE"
sPLACED = reserved "PLACED"
sPLUS = reserved "PLUS"
sPORT = reserved "PORT"
sPRI = reserved "PRI"
sPROC = reserved "PROC"
sPROCESSOR = reserved "PROCESSOR"
sPROTOCOL = reserved "PROTOCOL"
sREAL32 = reserved "REAL32"
sREAL64 = reserved "REAL64"
sRECORD = reserved "RECORD"
sREM = reserved "REM"
sRESHAPES = reserved "RESHAPES"
sRESULT = reserved "RESULT"
sRETYPES = reserved "RETYPES"
sROUND = reserved "ROUND"
sSEQ = reserved "SEQ"
sSIZE = reserved "SIZE"
sSKIP = reserved "SKIP"
sSTOP = reserved "STOP"
sTIMER = reserved "TIMER"
sTIMES = reserved "TIMES"
sTRUE = reserved "TRUE"
sTRUNC = reserved "TRUNC"
sTYPE = reserved "TYPE"
sVAL = reserved "VAL"
sVALOF = reserved "VALOF"
sWHILE = reserved "WHILE"
sMainMarker = reserved mainMarker

-- XXX could handle VALOF by translating each step to one { and matching multiple ones?
indent = symbol "{"
outdent = symbol "}"
eol = symbol "@"

-- -------------------------------------------------------------

-- These productions are based on the syntax in the occam2.1 manual.

-- The way productions should work is that each production should only consume input if it's sure that it's unambiguous.

abbreviation
    =   try (do { n <- name ; sIS ; v <- variable ; sColon ; eol ; return $ OcIs n v })
    <|> try (do { s <- specifier ; n <- name ; sIS ; v <- variable ; sColon ; eol ; return $ OcIsType s n v })
    <|> do {  sVAL ;
              try (do { n <- name ; sIS ; e <- expression ; sColon ; eol ; return $ OcValIs n e })
              <|> do { s <- specifier ; n <- name ; sIS ; e <- expression ; sColon ; eol ; return $ OcValIsType s n e } }
    <?> "abbreviation"

actual
    =   expression
    <|> variable
    <|> channel
    <?> "actual"

allocation
    =   do { sPLACE ; n <- name ; sAT ; e <- expression ; sColon ; eol ; return $ OcPlace n e }
    <?> "allocation"

alternation
    =   do {  sALT ;
              do { eol ; indent ; as <- many1 alternative ; outdent ; return $ OcAlt as }
              <|> do { r <- replicator ; eol ; indent ; a <- alternative ; outdent ; return $ OcAltRep r a } }
    <|> do {  sPRI ; sALT ;
              do { eol ; indent ; as <- many1 alternative ; outdent ; return $ OcPriAlt as }
              <|> do { r <- replicator ; eol ; indent ; a <- alternative ; outdent ; return $ OcPriAltRep r a } }
    <?> "alternation"

alternative
    =   guardedAlternative
    <|> alternation
    <|> try (do { b <- boolean ; sAmp ; c <- channel ; sQuest ; sCASE ; eol ; indent ; vs <- many1 variant ; outdent ; return $ OcInCaseGuard b c vs })
    <|> try (do { c <- channel ; sQuest ; sCASE ; eol ; indent ; vs <- many1 variant ; outdent ; return $ OcInCase c vs })
    <|> do { s <- specification ; a <- alternative ; return $ OcDecl s a }
    <?> "alternative"

assignment
    =   do { vs <- variableList ; sAssign ; es <- expressionList ; eol ; return $ OcAssign vs es }
    <?> "assignment"

base
    =   expression
    <?> "base"

boolean
    =   expression
    <?> "boolean"

byte
    =   lexeme (do { char '\'' ; s <- character ; char '\'' ; return $ OcLitByte s })
    <?> "byte"

caseExpression
    =   expression
    <?> "caseExpression"

caseInput
    =   do { c <- channel ; sQuest ; sCASE ; eol ; indent ; vs <- many1 variant ; outdent ; return $ OcInCase c vs }
    <?> "caseInput"

-- This is also used for timers and ports, since the syntax is identical (and
-- the parser really can't tell at this stage which is which).
channel
    =   do { v <- channel' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl OcSub v es }
    <?> "channel"

channel'
    =   try name
    <|> try (do { sLeft ; n <- channel ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ OcSubFromFor n e f })
    <|> try (do { sLeft ; n <- channel ; sFROM ; e <- expression ; sRight ; return $ OcSubFrom n e })
    <|> do { sLeft ; n <- channel ; sFOR ; e <- expression ; sRight ; return $ OcSubFor n e }
    <?> "channel'"

-- FIXME should probably make CHAN INT work, since that'd be trivial...
channelType
    =   do { sCHAN ; sOF ; p <- protocol ; return $ OcChanOf p }
    <|> try (do { sLeft ; s <- expression ; sRight ; t <- channelType ; return $ OcArray s t })
    <?> "channelType"

-- FIXME this isn't at all the right way to return the character!
character
    =   try (do { char '*' ;
                  do { char '#' ; a <- hexDigit ; b <- hexDigit ; return $ ['*', '#', a, b] }
                  <|> do { c <- anyChar ; return $ ['*', c] } })
    <|> do { c <- anyChar ; return $ [c] }
    <?> "character"

occamChoice
    =   guardedChoice
    <|> conditional
    <|> do { s <- try specification ; c <- occamChoice ; return $ OcDecl s c }
    <?> "choice"

conditional
    =   do {  sIF ;
              do { eol ; indent ; cs <- many1 occamChoice ; outdent ; return $ OcIf cs }
              <|> do { r <- replicator ; eol ; indent ; c <- occamChoice ; outdent ; return $ OcIfRep r c } }
    <?> "conditional"

conversion
    =   do  t <- dataType
            do { sROUND ; o <- operand ; return $ OcRound t o } <|> do { sTRUNC ; o <- operand ; return $ OcTrunc t o } <|> do { o <- operand ; return $ OcConv t o }
    <?> "conversion"

occamCount
    =   expression
    <?> "count"

dataType
    =   do { sBOOL ; return $ OcBool }
    <|> do { sBYTE ; return $ OcByte }
    <|> do { sINT ; return $ OcInt }
    <|> do { sINT16 ; return $ OcInt16 }
    <|> do { sINT32 ; return $ OcInt32 }
    <|> do { sINT64 ; return $ OcInt64 }
    <|> do { sREAL32 ; return $ OcReal32 }
    <|> do { sREAL64 ; return $ OcReal64 }
    <|> try (do { sLeft ; s <- expression ; sRight ; t <- dataType ; return $ OcArray s t })
    <|> name
    <?> "data type"

declType
    =   dataType
    <|> channelType
    <|> timerType
    <|> portType

-- FIXME this originally had four lines like this, one for each of the above;
-- it might be nicer to generate a different Node for each type of declaration
declaration
    =   do { d <- declType ; ns <- sepBy1 name sComma ; sColon ; eol ; return $ OcVars d ns }
    <?> "declaration"

definition
    =   do {  sDATA ; sTYPE ; n <- name ;
              do {sIS ; t <- dataType ; sColon ; eol ; return $ OcDataType n t }
              <|> do { eol ; indent ; t <- structuredType ; outdent ; sColon ; eol ; return $ OcDataType n t } }
    <|> do {  sPROTOCOL ; n <- name ;
              do { sIS ; p <- sequentialProtocol ; sColon ; eol ; return $ OcProtocol n p }
              <|> do { eol ; indent ; sCASE ; eol ; indent ; ps <- many1 taggedProtocol ; outdent ; outdent ; sColon ; eol ; return $ OcTaggedProtocol n ps } }
    <|> do { sPROC ; n <- name ; fs <- formalList ; eol ; indent ; p <- process ; outdent ; sColon ; eol ; return $ OcProc n fs p }
    <|> try (do { rs <- sepBy1 dataType sComma ; (n, fs) <- functionHeader ;
                  do { sIS ; el <- expressionList ; sColon ; eol ; return $ OcFuncIs n rs fs el }
                  <|> do { eol ; indent ; vp <- valueProcess ; outdent ; sColon ; eol ; return $ OcFunc n rs fs vp } })
    <|> try (do { s <- specifier ; n <- name ;
                  do { sRETYPES ; v <- variable ; sColon ; eol ; return $ OcRetypes s n v }
                  <|> do { try sRESHAPES ; v <- variable ; sColon ; eol ; return $ OcReshapes s n v } })
    <|> do {  sVAL ; s <- specifier ; n <- name ;
              do { sRETYPES ; v <- variable ; sColon ; eol ; return $ OcValRetypes s n v }
              <|> do { sRESHAPES ; v <- variable ; sColon ; eol ; return $ OcValReshapes s n v } }
    <?> "definition"

digits
    =   many1 digit
    <?> "digits"

dyadicOperator
    =   do { reservedOp "+" ; return $ OcAdd }
    <|> do { reservedOp "-" ; return $ OcSubtr }
    <|> do { reservedOp "*" ; return $ OcMul }
    <|> do { reservedOp "/" ; return $ OcDiv }
    <|> do { reservedOp "\\" ; return $ OcMod }
    <|> do { sREM ; return $ OcRem }
    <|> do { sPLUS ; return $ OcPlus }
    <|> do { sMINUS ; return $ OcMinus }
    <|> do { sTIMES ; return $ OcTimes }
    <|> do { reservedOp "/\\" ; return $ OcBitAnd }
    <|> do { reservedOp "\\/" ; return $ OcBitOr }
    <|> do { reservedOp "><" ; return $ OcBitXor }
    <|> do { sBITAND ; return $ OcBitAnd }
    <|> do { sBITOR ; return $ OcBitOr }
    <|> do { sAND ; return $ OcAnd }
    <|> do { sOR ; return $ OcOr }
    <|> do { reservedOp "=" ; return $ OcEq }
    <|> do { reservedOp "<>" ; return $ OcNEq }
    <|> do { reservedOp "<" ; return $ OcLess }
    <|> do { reservedOp ">" ; return $ OcMore }
    <|> do { reservedOp "<=" ; return $ OcLessEq }
    <|> do { reservedOp ">=" ; return $ OcMoreEq }
    <|> do { sAFTER ; return $ OcAfter }
    <?> "dyadicOperator"

occamExponent
    =   try (do { c <- oneOf "+-" ; d <- digits ; return $ c : d })
    <?> "exponent"

expression :: Parser Node
expression
    =   try (do { o <- monadicOperator ; v <- operand ; return $ o v })
    <|> do { a <- sMOSTPOS ; t <- dataType ; return $ OcMostPos t }
    <|> do { a <- sMOSTNEG ; t <- dataType ; return $ OcMostNeg t }
    <|> do { a <- sSIZE ; t <- dataType ; return $ OcSize t }
    <|> try (do { a <- operand ; o <- dyadicOperator ; b <- operand ; return $ o a b })
    <|> try conversion
    <|> operand
    <?> "expression"

expressionList
    =   try (do { n <- name ; sLeftR ; as <- sepBy expression sComma ; sRightR ; return $ OcCall n as })
    <|> do { es <- sepBy1 expression sComma ; return $ OcExpList es }
-- XXX value process
    <?> "expressionList"

fieldName
    =   name
    <?> "fieldName"

-- This is rather different from the grammar.
-- FIXME should this lot actually be done in a pass? probably...
formalList
    =   do { sLeftR ; fs <- sepBy formalArg sComma ; sRightR ; return $ markTypes fs }
    <?> "formalList"
    where
      formalArg :: Parser (Maybe Node, Node)
      formalArg =   try (do { sVAL ; s <- specifier ; n <- name ; return $ (Just (OcVal s), n) })
                <|> try (do { s <- specifier ; n <- name ; return $ (Just s, n) })
                <|> try (do { n <- name ; return $ (Nothing, n) })

      markTypes :: [(Maybe Node, Node)] -> [Node]
      markTypes [] = []
      markTypes ((Nothing, _):_) = error "Formal list must start with a type"
      markTypes ((Just ft,fn):is) = (OcFormal ft fn) : markRest ft is

      markRest :: Node -> [(Maybe Node, Node)] -> [Node]
      markRest _ [] = []
      markRest t ((Nothing, n):is) = (OcFormal t n) : markRest t is
      markRest _ ((Just t, n):is) = (OcFormal t n) : markRest t is

functionHeader
    =   do { sFUNCTION ; n <- name ; fs <- formalList ; return $ (n, fs) }
    <?> "functionHeader"

guard
    =   try input
    <|> try (do { b <- boolean ; sAmp ; i <- input ; return $ OcGuarded b i })
    <|> try (do { b <- boolean ; sAmp ; sSKIP ; eol ; return $ OcGuarded b OcSkip })
    <?> "guard"

guardedAlternative
    =   do { g <- guard ; indent ; p <- process ; outdent ; return $ OcGuarded g p }
    <?> "guardedAlternative"

guardedChoice
    =   do { b <- boolean ; eol ; indent ; p <- process ; outdent ; return $ OcGuarded b p }
    <?> "guardedChoice"

hexDigits
    =   do { d <- many1 hexDigit ; return $ OcLitHex d }
    <?> "hexDigits"

-- XXX how does the syntax handle multiline regular CASE inputs?
-- chan ? CASE
--   foo
--     ...

input
    =   do  c <- channel
            sQuest
            (do { sCASE ; tl <- taggedList ; eol ; return $ OcInTag c tl }
             <|> do { sAFTER ; e <- expression ; eol ; return $ OcInAfter c e }
             <|> do { is <- sepBy1 inputItem sSemi ; eol ; return $ OcIn c is })
    <?> "input"

inputItem
    =   try (do { v <- variable ; sColons ; w <- variable ; return $ OcCounted v w })
    <|> variable
    <?> "inputItem"

integer
    =   try (do { d <- lexeme digits ; return $ OcLitInt d })
    <|> do { char '#' ; d <- lexeme hexDigits ; return $ d }
    <?> "integer"

literal
    =   try real
    <|> try integer
    <|> try byte
    <|> try (do { v <- real ; sLeftR ; t <- dataType ; sRightR ; return $ OcTypedLit t v })
    <|> try (do { v <- integer ; sLeftR ; t <- dataType ; sRightR ; return $ OcTypedLit t v })
    <|> try (do { v <- byte ; sLeftR ; t <- dataType ; sRightR ; return $ OcTypedLit t v })
    <|> try (do { sTRUE ; return $ OcTrue })
    <|> do { sFALSE ; return $ OcFalse }
    <?> "literal"

loop
    =   do { sWHILE ; b <- boolean ; eol ; indent ; p <- process ; outdent ; return $ OcWhile b p }

monadicOperator
    =   do { reservedOp "-" ; return $ OcMonSub }
    <|> do { sMINUS ; return $ OcMonSub }
    <|> do { reservedOp "~" ; return $ OcMonBitNot }
    <|> do { sBITNOT ; return $ OcMonBitNot }
    <|> do { sNOT ; return $ OcMonNot }
    <|> do { sSIZE ; return $ OcSize }
    <?> "monadicOperator"

name
    =   do { s <- identifier ; return $ OcName s }
    <?> "name"

occamString
    =   lexeme (do { char '"' ; s <- many (noneOf "\"") ; char '"' ; return $ OcLitString s })
    <?> "string"

operand
    =   do { v <- operand' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl OcSub v es }
    <?> "operand"

operand'
    =   try variable
    <|> try literal
    <|> try table
    <|> try (do { sLeftR ; e <- expression ; sRightR ; return e })
-- XXX value process
    <|> try (do { n <- name ; sLeftR ; as <- sepBy expression sComma ; sRightR ; return $ OcCall n as })
    <|> try (do { sBYTESIN ; sLeftR ; o <- operand ; sRightR ; return $ OcBytesIn o })
    <|> try (do { sBYTESIN ; sLeftR ; o <- dataType ; sRightR ; return $ OcBytesIn o })
    <|> try (do { sOFFSETOF ; sLeftR ; n <- name ; sComma ; f <- fieldName ; sRightR ; return $ OcOffsetOf n f })
    <?> "operand'"

occamOption
    =   try (do { ces <- sepBy caseExpression sComma ; eol ; indent ; p <- process ; outdent ; return $ OcCaseExps ces p })
    <|> try (do { sELSE ; eol ; indent ; p <- process ; outdent ; return $ OcElse p })
    <|> do { s <- specification ; o <- occamOption ; return $ OcDecl s o }
    <?> "option"

-- XXX This can't tell at parse time in "c ! x; y" whether x is a variable or a tag...
-- ... so this now wants "c ! CASE x" if it's a tag, to match input.
output
    =   do  c <- channel
            sBang
            (do { sCASE ; t <- tag ; sSemi ; os <- sepBy1 outputItem sSemi ; eol ; return $ OcOutCase c t os }
             <|> do { sCASE ; t <- tag ; eol ; return $ OcOutCase c t [] }
             <|> do { os <- sepBy1 outputItem sSemi ; eol ; return $ OcOut c os })
    <?> "output"

outputItem
    =   try (do { a <- expression ; sColons ; b <- expression ; return $ OcCounted a b })
    <|> expression
    <?> "outputItem"

parallel
    =   do { sPAR ; do { eol ; indent ; ps <- many1 process ; outdent ; return $ OcPar ps } <|> do { r <- replicator ; eol ; indent ; p <- process ; outdent ; return $ OcParRep r p } }
    <|> do { sPRI ; sPAR ; do { eol ; indent ; ps <- many1 process ; outdent ; return $ OcPriPar ps } <|> do { r <- replicator ; eol ; indent ; p <- process ; outdent ; return $ OcPriParRep r p } }
    <|> placedpar
    <?> "parallel"

-- XXX PROCESSOR as a process isn't really legal, surely?
placedpar
    =   do { sPLACED ; sPAR ; do { eol ; indent ; ps <- many1 placedpar ; outdent ; return $ OcPlacedPar ps } <|> do { r <- replicator ; eol ; indent ; p <- placedpar ; outdent ; return $ OcPlacedParRep r p } }
    <|> do { sPROCESSOR ; e <- expression ; eol ; indent ; p <- process ; outdent ; return $ OcProcessor e p }
    <?> "placedpar"

portType
    =   do { sPORT ; sOF ; p <- protocol ; return $ OcPortOf p }
    <|> do { try sLeft ; s <- try expression ; try sRight ; t <- portType ; return $ OcArray s t }
    <?> "portType"

procInstance
    =   do { n <- name ; sLeftR ; as <- sepBy actual sComma ; sRightR ; eol ; return $ OcProcCall n as }
    <?> "procInstance"

process
    =   try assignment
    <|> try input
    <|> try output
    <|> do { sSKIP ; eol ; return $ OcSkip }
    <|> do { sSTOP ; eol ; return $ OcStop }
    <|> occamSequence
    <|> conditional
    <|> selection
    <|> loop
    <|> try parallel
    <|> alternation
    <|> try caseInput
    <|> try procInstance
    <|> do { sMainMarker ; eol ; return $ OcMainProcess }
    <|> do { a <- allocation ; p <- process ; return $ OcDecl a p }
    <|> do { s <- specification ; p <- process ; return $ OcDecl s p }
    <?> "process"

protocol
    =   try name
    <|> simpleProtocol
    <?> "protocol"

real
    =   try (do { l <- digits ; char '.' ; r <- digits ; char 'e' ; e <- lexeme occamExponent ; return $ OcLitReal (l ++ "." ++ r ++ "e" ++ e) })
    <|> do { l <- digits ; char '.' ; r <- lexeme digits ; return $ OcLitReal (l ++ "." ++ r) }
    <?> "real"

replicator
    =   do { n <- name ; sEq ; b <- base ; sFOR ; c <- occamCount ; return $ OcFor n b c }
    <?> "replicator"

selection
    =   do { sCASE ; s <- selector ; eol ; indent ; os <- many1 occamOption ; outdent ; return $ OcCase s os }
    <?> "selection"

selector
    =   expression
    <?> "selector"

occamSequence
    =   do  sSEQ
            (do { eol ; indent ; ps <- many1 process ; outdent ; return $ OcSeq ps }
             <|> do { r <- replicator ; eol ; indent ; p <- process ; outdent ; return $ OcSeqRep r p })
    <?> "sequence"

sequentialProtocol
    =   do { l <- try $ sepBy1 simpleProtocol sSemi ; return $ l }
    <?> "sequentialProtocol"

simpleProtocol
    =   try (do { l <- dataType ; sColons ; sLeft ; sRight ; r <- dataType ; return $ OcCounted l r })
    <|> dataType
    <|> do { sANY ; return $ OcAny }
    <?> "simpleProtocol"

specification
    =   try declaration
    <|> try abbreviation
    <|> definition
    <?> "specification"

specifier :: Parser Node
specifier
    =   try dataType
    <|> try channelType
    <|> try timerType
    <|> try portType
    <|> try (do { sLeft ; sRight ; s <- specifier ; return $ OcArrayUnsized s })
    <|> do { sLeft ; e <- expression ; sRight ; s <- specifier ; return $ OcArray e s }
    <?> "specifier"

structuredType
    =   try (do { sRECORD ; eol ; indent ; fs <- many1 structuredTypeField ; outdent ; return $ OcRecord fs })
    <|> do { sPACKED ; sRECORD ; eol ; indent ; fs <- many1 structuredTypeField ; outdent ; return $ OcPackedRecord fs }
    <?> "structuredType"

-- FIXME this should use the same type-folding code as proc/func definitions
structuredTypeField
    =   do { t <- dataType ; fs <- many1 fieldName ; sColon ; eol ; return $ OcFields t fs }
    <?> "structuredTypeField"

-- i.e. array literal
table
    =   do { v <- table' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl OcSub v es }
    <?> "table"

table'
    =   try occamString
    <|> try (do { s <- occamString ; sLeftR ; n <- name ; sRightR ; return $ OcTypedLit n s })
    <|> do {  sLeft ;
              try (do { es <- sepBy1 expression sComma ; sRight ; return $ OcLitArray es })
              <|> try (do { n <- table ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ OcSubFromFor n e f })
              <|> try (do { n <- table ; sFROM ; e <- expression ; sRight ; return $ OcSubFrom n e })
              <|> do { n <- table ; sFOR ; e <- expression ; sRight ; return $ OcSubFor n e } }
    <?> "table'"

tag
    =   name
    <?> "tag"

taggedList
    =   try (do { t <- tag ; sSemi ; is <- sepBy1 inputItem sSemi ; return $ OcTag t is })
    <|> do { t <- tag ; return $ OcTag t [] }
    <?> "taggedList"

taggedProtocol
    =   try (do { t <- tag ; eol ; return $ OcTag t [] })
    <|> try (do { t <- tag ; sSemi ; sp <- sequentialProtocol ; eol ; return $ OcTag t sp })

timerType
    =   do { sTIMER ; return $ OcTimer }
    <|> do { try sLeft ; s <- try expression ; try sRight ; t <- timerType ; return $ OcArray s t }
    <?> "timerType"

valueProcess
    =   try (do { sVALOF ; eol ; indent ; p <- process ; sRESULT ; el <- expressionList ; eol ; outdent ; return $ OcValOf p el })
    <|> do { s <- specification ; v <- valueProcess ; return $ OcDecl s v }

variable
    =   do { v <- variable' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl OcSub v es }
    <?> "variable"

variable'
    =   try name
    <|> try (do { sLeft ; n <- variable ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ OcSubFromFor n e f })
    <|> try (do { sLeft ; n <- variable ; sFROM ; e <- expression ; sRight ; return $ OcSubFrom n e })
    <|> do { sLeft ; n <- variable ; sFOR ; e <- expression ; sRight ; return $ OcSubFor n e }
    <?> "variable'"

variableList
    =   do { vs <- sepBy1 variable sComma ; return $ vs }
    <?> "variableList"

variant
    =   try (do { t <- taggedList ; eol ; indent ; p <- process ; outdent ; return $ OcVariant t p })
    <|> do { s <- specification ; v <- variant ; return $ OcDecl s v }
    <?> "variant"

-- -------------------------------------------------------------

-- This is only really true once we've tacked a process onto the bottom; a
-- source file is really a series of specifications, but the later ones need to
-- have the earlier ones in scope, so we can't parse them separately.

sourceFile = do { whiteSpace ; process }

-- -------------------------------------------------------------

-- XXX this doesn't handle multi-line strings
-- XXX or VALOF processes

countIndent :: String -> Int
countIndent (' ':' ':cs) = 1 + (countIndent cs)
countIndent (' ':cs) = error "Bad indentation"
countIndent _ = 0

stripIndent :: String -> String
stripIndent (' ':cs) = stripIndent cs
stripIndent cs = cs

stripComment :: String -> String
stripComment [] = []
stripComment ('-':'-':s) = []
stripComment ('"':s) = '"' : stripCommentInString s
stripComment (c:s) = c : stripComment s

stripCommentInString :: String -> String
stripCommentInString [] = error "In string at end of line"
stripCommentInString ('"':s) = '"' : stripComment s
stripCommentInString (c:s) = c : stripCommentInString s

flatten :: [String] -> String
flatten ls = concat $ intersperse "\n" $ flatten' ls 0
  where
    rep n i = take n (repeat i)
    flatten' [] level = [rep level '}']
    flatten' (s:ss) level
      | stripped == ""   = "" : flatten' ss level
      | newLevel > level = (rep (newLevel - level) '{' ++ stripped) : rest
      | newLevel < level = (rep (level - newLevel) '}' ++ stripped) : rest
      | otherwise        = stripped : rest
      where newLevel = countIndent s
            stripped' = stripIndent $ stripComment s
            stripped = if stripped' == "" then "" else (stripped' ++ "@")
            rest = flatten' ss newLevel

-- -------------------------------------------------------------

-- XXX Doesn't handle preprocessor instructions.

prepare d = flatten $ lines (d ++ "\n" ++ mainMarker)

numberedListing :: String -> String
numberedListing s = concat $ intersperse "\n" $ [(show n) ++ ": " ++ s | (n, s) <- zip [1..] (lines s)]

parseSourceFile :: String -> IO Node
parseSourceFile fn
  = do  f <- IO.openFile fn IO.ReadMode
        d <- IO.hGetContents f
        let prep = prepare d
        putStrLn $ "Prepared: " ++ numberedListing prep
        return $ case (parse sourceFile "occam" prep) of
           Left err -> error ("Parsing error: " ++ (show err))
           Right defs -> defs

