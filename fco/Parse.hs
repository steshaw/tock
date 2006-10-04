-- Parse occam code

module Parse (readSource, parseSource) where

import Data.List
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language (emptyDef)
import qualified IO

import qualified PT as N

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
    =   try (do { n <- name ; sIS ; v <- variable ; sColon ; eol ; return $ N.Is n v })
    <|> try (do { s <- specifier ; n <- name ; sIS ; v <- variable ; sColon ; eol ; return $ N.IsType s n v })
    <|> do {  sVAL ;
              try (do { n <- name ; sIS ; e <- expression ; sColon ; eol ; return $ N.ValIs n e })
              <|> do { s <- specifier ; n <- name ; sIS ; e <- expression ; sColon ; eol ; return $ N.ValIsType s n e } }
    <?> "abbreviation"

actual
    =   expression
    <|> variable
    <|> channel
    <?> "actual"

allocation
    =   do { sPLACE ; n <- name ; sAT ; e <- expression ; sColon ; eol ; return $ N.Place n e }
    <?> "allocation"

alternation
    =   do {  sALT ;
              do { eol ; indent ; as <- many1 alternative ; outdent ; return $ N.Alt as }
              <|> do { r <- replicator ; eol ; indent ; a <- alternative ; outdent ; return $ N.AltRep r a } }
    <|> do {  sPRI ; sALT ;
              do { eol ; indent ; as <- many1 alternative ; outdent ; return $ N.PriAlt as }
              <|> do { r <- replicator ; eol ; indent ; a <- alternative ; outdent ; return $ N.PriAltRep r a } }
    <?> "alternation"

-- The reason the CASE guards end up here is because they have to be handled
-- specially: you can't tell until parsing the guts of the CASE what the processes
-- are.
alternative
    =   guardedAlternative
    <|> alternation
    <|> try (do { b <- boolean ; sAmp ; c <- channel ; sQuest ; sCASE ; eol ; indent ; vs <- many1 variant ; outdent ; return $ N.CondGuard b (N.In c (N.InCase vs)) })
    <|> try (do { c <- channel ; sQuest ; sCASE ; eol ; indent ; vs <- many1 variant ; outdent ; return $ N.In c (N.InCase vs) })
    <|> do { s <- specification ; a <- alternative ; return $ N.Decl s a }
    <?> "alternative"

assignment
    =   do { vs <- variableList ; sAssign ; es <- expressionList ; eol ; return $ N.Assign vs es }
    <?> "assignment"

base
    =   expression
    <?> "base"

boolean
    =   expression
    <?> "boolean"

byte
    =   lexeme (do { char '\'' ; s <- character ; char '\'' ; return $ N.LitByte s })
    <?> "byte"

caseExpression
    =   expression
    <?> "caseExpression"

caseInput
    =   do { c <- channel ; sQuest ; sCASE ; eol ; indent ; vs <- many1 variant ; outdent ; return $ N.In c (N.InCase vs) }
    <?> "caseInput"

-- This is also used for timers and ports, since the syntax is identical (and
-- the parser really can't tell at this stage which is which).
channel
    =   do { v <- channel' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\e s -> N.Sub (N.SubPlain s) e) v es }
    <?> "channel"

channel'
    =   try name
    <|> try (do { sLeft ; n <- channel ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ N.Sub (N.SubFromFor e f) n })
    <|> try (do { sLeft ; n <- channel ; sFROM ; e <- expression ; sRight ; return $ N.Sub (N.SubFrom e) n })
    <|> do { sLeft ; n <- channel ; sFOR ; e <- expression ; sRight ; return $ N.Sub (N.SubFor e) n }
    <?> "channel'"

-- FIXME should probably make CHAN INT work, since that'd be trivial...
channelType
    =   do { sCHAN ; sOF ; p <- protocol ; return $ N.ChanOf p }
    <|> try (do { sLeft ; s <- expression ; sRight ; t <- channelType ; return $ N.Array s t })
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
    <|> do { s <- try specification ; c <- occamChoice ; return $ N.Decl s c }
    <?> "choice"

conditional
    =   do {  sIF ;
              do { eol ; indent ; cs <- many1 occamChoice ; outdent ; return $ N.If cs }
              <|> do { r <- replicator ; eol ; indent ; c <- occamChoice ; outdent ; return $ N.IfRep r c } }
    <?> "conditional"

conversion
    =   do  t <- dataType
            do { sROUND ; o <- operand ; return $ N.Round t o } <|> do { sTRUNC ; o <- operand ; return $ N.Trunc t o } <|> do { o <- operand ; return $ N.Conv t o }
    <?> "conversion"

occamCount
    =   expression
    <?> "count"

dataType
    =   do { sBOOL ; return $ N.Bool }
    <|> do { sBYTE ; return $ N.Byte }
    <|> do { sINT ; return $ N.Int }
    <|> do { sINT16 ; return $ N.Int16 }
    <|> do { sINT32 ; return $ N.Int32 }
    <|> do { sINT64 ; return $ N.Int64 }
    <|> do { sREAL32 ; return $ N.Real32 }
    <|> do { sREAL64 ; return $ N.Real64 }
    <|> try (do { sLeft ; s <- expression ; sRight ; t <- dataType ; return $ N.Array s t })
    <|> name
    <?> "data type"

declType
    =   dataType
    <|> channelType
    <|> timerType
    <|> portType

-- FIXME this originally had four lines like this, one for each of the above;
-- it might be nicer to generate a different N.Node for each type of declaration
declaration
    =   do { d <- declType ; ns <- sepBy1 name sComma ; sColon ; eol ; return $ N.Vars d ns }
    <?> "declaration"

definition
    =   do {  sDATA ; sTYPE ; n <- name ;
              do {sIS ; t <- dataType ; sColon ; eol ; return $ N.DataType n t }
              <|> do { eol ; indent ; t <- structuredType ; outdent ; sColon ; eol ; return $ N.DataType n t } }
    <|> do {  sPROTOCOL ; n <- name ;
              do { sIS ; p <- sequentialProtocol ; sColon ; eol ; return $ N.Protocol n p }
              <|> do { eol ; indent ; sCASE ; eol ; indent ; ps <- many1 taggedProtocol ; outdent ; outdent ; sColon ; eol ; return $ N.TaggedProtocol n ps } }
    <|> do { sPROC ; n <- name ; fs <- formalList ; eol ; indent ; p <- process ; outdent ; sColon ; eol ; return $ N.Proc n fs p }
    <|> try (do { rs <- sepBy1 dataType sComma ; (n, fs) <- functionHeader ;
                  do { sIS ; el <- expressionList ; sColon ; eol ; return $ N.FuncIs n rs fs el }
                  <|> do { eol ; indent ; vp <- valueProcess ; outdent ; sColon ; eol ; return $ N.Func n rs fs vp } })
    <|> try (do { s <- specifier ; n <- name ;
                  do { sRETYPES ; v <- variable ; sColon ; eol ; return $ N.Retypes s n v }
                  <|> do { try sRESHAPES ; v <- variable ; sColon ; eol ; return $ N.Reshapes s n v } })
    <|> do {  sVAL ; s <- specifier ; n <- name ;
              do { sRETYPES ; v <- variable ; sColon ; eol ; return $ N.ValRetypes s n v }
              <|> do { sRESHAPES ; v <- variable ; sColon ; eol ; return $ N.ValReshapes s n v } }
    <?> "definition"

digits
    =   many1 digit
    <?> "digits"

dyadicOperator
    =   do { reservedOp "+" ; return $ N.Add }
    <|> do { reservedOp "-" ; return $ N.Subtr }
    <|> do { reservedOp "*" ; return $ N.Mul }
    <|> do { reservedOp "/" ; return $ N.Div }
    <|> do { reservedOp "\\" ; return $ N.Rem }
    <|> do { sREM ; return $ N.Rem }
    <|> do { sPLUS ; return $ N.Plus }
    <|> do { sMINUS ; return $ N.Minus }
    <|> do { sTIMES ; return $ N.Times }
    <|> do { reservedOp "/\\" ; return $ N.BitAnd }
    <|> do { reservedOp "\\/" ; return $ N.BitOr }
    <|> do { reservedOp "><" ; return $ N.BitXor }
    <|> do { sBITAND ; return $ N.BitAnd }
    <|> do { sBITOR ; return $ N.BitOr }
    <|> do { sAND ; return $ N.And }
    <|> do { sOR ; return $ N.Or }
    <|> do { reservedOp "=" ; return $ N.Eq }
    <|> do { reservedOp "<>" ; return $ N.NEq }
    <|> do { reservedOp "<" ; return $ N.Less }
    <|> do { reservedOp ">" ; return $ N.More }
    <|> do { reservedOp "<=" ; return $ N.LessEq }
    <|> do { reservedOp ">=" ; return $ N.MoreEq }
    <|> do { sAFTER ; return $ N.After }
    <?> "dyadicOperator"

occamExponent
    =   try (do { c <- oneOf "+-" ; d <- digits ; return $ c : d })
    <?> "exponent"

expression :: Parser N.Node
expression
    =   try (do { o <- monadicOperator ; v <- operand ; return $ N.MonadicOp o v })
    <|> do { a <- sMOSTPOS ; t <- dataType ; return $ N.MostPos t }
    <|> do { a <- sMOSTNEG ; t <- dataType ; return $ N.MostNeg t }
    <|> do { a <- sSIZE ; t <- dataType ; return $ N.Size t }
    <|> try (do { a <- operand ; o <- dyadicOperator ; b <- operand ; return $ N.DyadicOp o a b })
    <|> try conversion
    <|> operand
    <?> "expression"

expressionList
    =   try (do { n <- name ; sLeftR ; as <- sepBy expression sComma ; sRightR ; return $ N.Call n as })
    <|> do { es <- sepBy1 expression sComma ; return $ N.ExpList es }
-- XXX value process
    <?> "expressionList"

fieldName
    =   name
    <?> "fieldName"

-- This is rather different from the grammar, since I had some difficulty
-- getting Parsec to parse it as a list of lists of arguments.
formalList
    =   do { sLeftR ; fs <- sepBy formalArg sComma ; sRightR ; return $ markTypes fs }
    <?> "formalList"
    where
      formalArg :: Parser (Maybe N.Node, N.Node)
      formalArg =   try (do { sVAL ; s <- specifier ; n <- name ; return $ (Just (N.Val s), n) })
                <|> try (do { s <- specifier ; n <- name ; return $ (Just s, n) })
                <|> try (do { n <- name ; return $ (Nothing, n) })

      markTypes :: [(Maybe N.Node, N.Node)] -> [N.Node]
      markTypes [] = []
      markTypes ((Nothing, _):_) = error "Formal list must start with a type"
      markTypes ((Just ft, fn):is) = markRest ft [fn] is

      markRest :: N.Node -> [N.Node] -> [(Maybe N.Node, N.Node)] -> [N.Node]
      markRest lt ns [] = [N.Formals lt ns]
      markRest lt ns ((Nothing, n):is) = markRest lt (ns ++ [n]) is
      markRest lt ns ((Just t, n):is) = (markRest lt ns []) ++ (markRest t [n] is)

functionHeader
    =   do { sFUNCTION ; n <- name ; fs <- formalList ; return $ (n, fs) }
    <?> "functionHeader"

guard
    =   try input
    <|> try (do { b <- boolean ; sAmp ; i <- input ; return $ N.CondGuard b i })
    <|> try (do { b <- boolean ; sAmp ; sSKIP ; eol ; return $ N.CondGuard b N.Skip })
    <?> "guard"

guardedAlternative
    =   do { g <- guard ; indent ; p <- process ; outdent ; return $ N.Guard g p }
    <?> "guardedAlternative"

guardedChoice
    =   do { b <- boolean ; eol ; indent ; p <- process ; outdent ; return $ N.Choice b p }
    <?> "guardedChoice"

hexDigits
    =   do { d <- many1 hexDigit ; return $ N.LitHex d }
    <?> "hexDigits"

input
    =   do  c <- channel
            sQuest
            (do { sCASE ; tl <- taggedList ; eol ; return $ N.In c (N.InTag tl) }
             <|> do { sAFTER ; e <- expression ; eol ; return $ N.In c (N.InAfter e) }
             <|> do { is <- sepBy1 inputItem sSemi ; eol ; return $ N.In c (N.InSimple is) })
    <?> "input"

inputItem
    =   try (do { v <- variable ; sColons ; w <- variable ; return $ N.Counted v w })
    <|> variable
    <?> "inputItem"

integer
    =   try (do { d <- lexeme digits ; return $ N.LitInt d })
    <|> do { char '#' ; d <- lexeme hexDigits ; return $ d }
    <?> "integer"

literal
    =   try real
    <|> try integer
    <|> try byte
    <|> try (do { v <- real ; sLeftR ; t <- dataType ; sRightR ; return $ N.TypedLit t v })
    <|> try (do { v <- integer ; sLeftR ; t <- dataType ; sRightR ; return $ N.TypedLit t v })
    <|> try (do { v <- byte ; sLeftR ; t <- dataType ; sRightR ; return $ N.TypedLit t v })
    <|> try (do { sTRUE ; return $ N.True })
    <|> do { sFALSE ; return $ N.False }
    <?> "literal"

loop
    =   do { sWHILE ; b <- boolean ; eol ; indent ; p <- process ; outdent ; return $ N.While b p }

monadicOperator
    =   do { reservedOp "-" ; return $ N.MonSub }
    <|> do { sMINUS ; return $ N.MonSub }
    <|> do { reservedOp "~" ; return $ N.MonBitNot }
    <|> do { sBITNOT ; return $ N.MonBitNot }
    <|> do { sNOT ; return $ N.MonNot }
    <|> do { sSIZE ; return $ N.MonSize }
    <?> "monadicOperator"

name
    =   do { s <- identifier ; return $ N.Name s }
    <?> "name"

occamString
    =   lexeme (do { char '"' ; s <- many (noneOf "\"") ; char '"' ; return $ N.LitString s })
    <?> "string"

operand
    =   do { v <- operand' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\e s -> N.Sub (N.SubPlain s) e) v es }
    <?> "operand"

operand'
    =   try variable
    <|> try literal
    <|> try table
    <|> try (do { sLeftR ; e <- expression ; sRightR ; return e })
-- XXX value process
    <|> try (do { n <- name ; sLeftR ; as <- sepBy expression sComma ; sRightR ; return $ N.Call n as })
    <|> try (do { sBYTESIN ; sLeftR ; o <- operand ; sRightR ; return $ N.BytesIn o })
    <|> try (do { sBYTESIN ; sLeftR ; o <- dataType ; sRightR ; return $ N.BytesIn o })
    <|> try (do { sOFFSETOF ; sLeftR ; n <- name ; sComma ; f <- fieldName ; sRightR ; return $ N.OffsetOf n f })
    <?> "operand'"

occamOption
    =   try (do { ces <- sepBy caseExpression sComma ; eol ; indent ; p <- process ; outdent ; return $ N.CaseExps ces p })
    <|> try (do { sELSE ; eol ; indent ; p <- process ; outdent ; return $ N.Else p })
    <|> do { s <- specification ; o <- occamOption ; return $ N.Decl s o }
    <?> "option"

-- XXX This can't tell at parse time in "c ! x; y" whether x is a variable or a tag...
-- ... so this now wants "c ! CASE x" if it's a tag, to match input.
-- We can fix this with a pass later...
output
    =   do  c <- channel
            sBang
            (do { sCASE ; t <- tag ; sSemi ; os <- sepBy1 outputItem sSemi ; eol ; return $ N.OutCase c t os }
             <|> do { sCASE ; t <- tag ; eol ; return $ N.OutCase c t [] }
             <|> do { os <- sepBy1 outputItem sSemi ; eol ; return $ N.Out c os })
    <?> "output"

outputItem
    =   try (do { a <- expression ; sColons ; b <- expression ; return $ N.Counted a b })
    <|> expression
    <?> "outputItem"

parallel
    =   do { sPAR ; do { eol ; indent ; ps <- many1 process ; outdent ; return $ N.Par ps } <|> do { r <- replicator ; eol ; indent ; p <- process ; outdent ; return $ N.ParRep r p } }
    <|> do { sPRI ; sPAR ; do { eol ; indent ; ps <- many1 process ; outdent ; return $ N.PriPar ps } <|> do { r <- replicator ; eol ; indent ; p <- process ; outdent ; return $ N.PriParRep r p } }
    <|> placedpar
    <?> "parallel"

-- XXX PROCESSOR as a process isn't really legal, surely?
placedpar
    =   do { sPLACED ; sPAR ; do { eol ; indent ; ps <- many1 placedpar ; outdent ; return $ N.PlacedPar ps } <|> do { r <- replicator ; eol ; indent ; p <- placedpar ; outdent ; return $ N.PlacedParRep r p } }
    <|> do { sPROCESSOR ; e <- expression ; eol ; indent ; p <- process ; outdent ; return $ N.Processor e p }
    <?> "placedpar"

portType
    =   do { sPORT ; sOF ; p <- protocol ; return $ N.PortOf p }
    <|> do { try sLeft ; s <- try expression ; try sRight ; t <- portType ; return $ N.Array s t }
    <?> "portType"

procInstance
    =   do { n <- name ; sLeftR ; as <- sepBy actual sComma ; sRightR ; eol ; return $ N.ProcCall n as }
    <?> "procInstance"

process
    =   try assignment
    <|> try input
    <|> try output
    <|> do { sSKIP ; eol ; return $ N.Skip }
    <|> do { sSTOP ; eol ; return $ N.Stop }
    <|> occamSequence
    <|> conditional
    <|> selection
    <|> loop
    <|> try parallel
    <|> alternation
    <|> try caseInput
    <|> try procInstance
    <|> do { sMainMarker ; eol ; return $ N.MainProcess }
    <|> do { a <- allocation ; p <- process ; return $ N.Decl a p }
    <|> do { s <- specification ; p <- process ; return $ N.Decl s p }
    <?> "process"

protocol
    =   try name
    <|> simpleProtocol
    <?> "protocol"

real
    =   try (do { l <- digits ; char '.' ; r <- digits ; char 'e' ; e <- lexeme occamExponent ; return $ N.LitReal (l ++ "." ++ r ++ "e" ++ e) })
    <|> do { l <- digits ; char '.' ; r <- lexeme digits ; return $ N.LitReal (l ++ "." ++ r) }
    <?> "real"

replicator
    =   do { n <- name ; sEq ; b <- base ; sFOR ; c <- occamCount ; return $ N.For n b c }
    <?> "replicator"

selection
    =   do { sCASE ; s <- selector ; eol ; indent ; os <- many1 occamOption ; outdent ; return $ N.Case s os }
    <?> "selection"

selector
    =   expression
    <?> "selector"

occamSequence
    =   do  sSEQ
            (do { eol ; indent ; ps <- many1 process ; outdent ; return $ N.Seq ps }
             <|> do { r <- replicator ; eol ; indent ; p <- process ; outdent ; return $ N.SeqRep r p })
    <?> "sequence"

sequentialProtocol
    =   do { l <- try $ sepBy1 simpleProtocol sSemi ; return $ l }
    <?> "sequentialProtocol"

simpleProtocol
    =   try (do { l <- dataType ; sColons ; sLeft ; sRight ; r <- dataType ; return $ N.Counted l r })
    <|> dataType
    <|> do { sANY ; return $ N.Any }
    <?> "simpleProtocol"

specification
    =   try declaration
    <|> try abbreviation
    <|> definition
    <?> "specification"

specifier :: Parser N.Node
specifier
    =   try dataType
    <|> try channelType
    <|> try timerType
    <|> try portType
    <|> try (do { sLeft ; sRight ; s <- specifier ; return $ N.ArrayUnsized s })
    <|> do { sLeft ; e <- expression ; sRight ; s <- specifier ; return $ N.Array e s }
    <?> "specifier"

structuredType
    =   try (do { sRECORD ; eol ; indent ; fs <- many1 structuredTypeField ; outdent ; return $ N.Record fs })
    <|> do { sPACKED ; sRECORD ; eol ; indent ; fs <- many1 structuredTypeField ; outdent ; return $ N.PackedRecord fs }
    <?> "structuredType"

-- FIXME this should use the same type-folding code as proc/func definitions
structuredTypeField
    =   do { t <- dataType ; fs <- many1 fieldName ; sColon ; eol ; return $ N.Fields t fs }
    <?> "structuredTypeField"

-- i.e. array literal
table
    =   do { v <- table' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\e s -> N.Sub (N.SubPlain s) e) v es }
    <?> "table"

table'
    =   try occamString
    <|> try (do { s <- occamString ; sLeftR ; n <- name ; sRightR ; return $ N.TypedLit n s })
    <|> do {  sLeft ;
              try (do { es <- sepBy1 expression sComma ; sRight ; return $ N.LitArray es })
              <|> try (do { n <- table ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ N.Sub (N.SubFromFor e f) n })
              <|> try (do { n <- table ; sFROM ; e <- expression ; sRight ; return $ N.Sub (N.SubFrom e) n })
              <|> do { n <- table ; sFOR ; e <- expression ; sRight ; return $ N.Sub (N.SubFor e) n } }
    <?> "table'"

tag
    =   name
    <?> "tag"

taggedList
    =   try (do { t <- tag ; sSemi ; is <- sepBy1 inputItem sSemi ; return $ N.Tag t is })
    <|> do { t <- tag ; return $ N.Tag t [] }
    <?> "taggedList"

taggedProtocol
    =   try (do { t <- tag ; eol ; return $ N.Tag t [] })
    <|> try (do { t <- tag ; sSemi ; sp <- sequentialProtocol ; eol ; return $ N.Tag t sp })

timerType
    =   do { sTIMER ; return $ N.Timer }
    <|> do { try sLeft ; s <- try expression ; try sRight ; t <- timerType ; return $ N.Array s t }
    <?> "timerType"

valueProcess
    =   try (do { sVALOF ; eol ; indent ; p <- process ; sRESULT ; el <- expressionList ; eol ; outdent ; return $ N.ValOf p el })
    <|> do { s <- specification ; v <- valueProcess ; return $ N.Decl s v }

variable
    =   do { v <- variable' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\e s -> N.Sub (N.SubPlain s) e) v es }
    <?> "variable"

variable'
    =   try name
    <|> try (do { sLeft ; n <- variable ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ N.Sub (N.SubFromFor e f) n })
    <|> try (do { sLeft ; n <- variable ; sFROM ; e <- expression ; sRight ; return $ N.Sub (N.SubFrom e) n })
    <|> do { sLeft ; n <- variable ; sFOR ; e <- expression ; sRight ; return $ N.Sub (N.SubFor e) n }
    <?> "variable'"

variableList
    =   do { vs <- sepBy1 variable sComma ; return $ vs }
    <?> "variableList"

variant
    =   try (do { t <- taggedList ; eol ; indent ; p <- process ; outdent ; return $ N.Variant t p })
    <|> do { s <- specification ; v <- variant ; return $ N.Decl s v }
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

preprocess :: String -> String
preprocess d = flatten $ lines (d ++ "\n" ++ mainMarker)

readSource :: String -> IO String
readSource fn = do
  f <- IO.openFile fn IO.ReadMode
  d <- IO.hGetContents f
  let prep = preprocess d
  return prep

-- -------------------------------------------------------------

parseSource :: String -> N.Node
parseSource prep
  = case (parse sourceFile "occam" prep) of
      Left err -> error ("Parsing error: " ++ (show err))
      Right defs -> defs

