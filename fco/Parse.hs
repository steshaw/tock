-- Parse occam code

module Parse (readSource, parseSource) where

import Data.List
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language (emptyDef)
import qualified IO

import qualified PT as N
import Metadata

-- -------------------------------------------------------------

md :: Parser Meta
md = do
  pos <- getPosition
  return $ [SourcePos (sourceName pos) (sourceLine pos) (sourceColumn pos)]

nd :: Meta -> N.NodeType -> N.Node
nd = N.Node

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
    =   try (do { m <- md ; n <- name ; sIS ; v <- variable ; sColon ; eol ; return $ nd m $ N.Is n v })
    <|> try (do { m <- md ; s <- specifier ; n <- name ; sIS ; v <- variable ; sColon ; eol ; return $ nd m $ N.IsType s n v })
    <|> do { m <- md ; sVAL ;
              try (do { n <- name ; sIS ; e <- expression ; sColon ; eol ; return $ nd m $ N.ValIs n e })
              <|> do { s <- specifier ; n <- name ; sIS ; e <- expression ; sColon ; eol ; return $ nd m $ N.ValIsType s n e } }
    <?> "abbreviation"

actual
    =   expression
    <|> variable
    <|> channel
    <?> "actual"

allocation
    =   do { m <- md ; sPLACE ; n <- name ; sAT ; e <- expression ; sColon ; eol ; return $ nd m $ N.Place n e }
    <?> "allocation"

alternation
    =   do {  m <- md ; sALT ;
              do { eol ; indent ; as <- many1 alternative ; outdent ; return $ nd m $ N.Alt as }
              <|> do { r <- replicator ; eol ; indent ; a <- alternative ; outdent ; return $ nd m $ N.AltRep r a } }
    <|> do {  m <- md ; sPRI ; sALT ;
              do { eol ; indent ; as <- many1 alternative ; outdent ; return $ nd m $ N.PriAlt as }
              <|> do { r <- replicator ; eol ; indent ; a <- alternative ; outdent ; return $ nd m $ N.PriAltRep r a } }
    <?> "alternation"

-- The reason the CASE guards end up here is because they have to be handled
-- specially: you can't tell until parsing the guts of the CASE what the processes
-- are.
alternative
    =   guardedAlternative
    <|> alternation
    <|> try (do { m <- md ; b <- boolean ; sAmp ; c <- channel ; sQuest ; sCASE ; eol ; indent ; vs <- many1 variant ; outdent ; return $ nd m $ N.CondGuard b (nd m $ N.In c (nd m $ N.InCase vs)) })
    <|> try (do { m <- md ; c <- channel ; sQuest ; sCASE ; eol ; indent ; vs <- many1 variant ; outdent ; return $ nd m $ N.In c (nd m $ N.InCase vs) })
    <|> do { m <- md ; s <- specification ; a <- alternative ; return $ nd m $ N.Decl s a }
    <?> "alternative"

assignment
    =   do { m <- md ; vs <- variableList ; sAssign ; es <- expressionList ; eol ; return $ nd m $ N.Assign vs es }
    <?> "assignment"

base
    =   expression
    <?> "base"

boolean
    =   expression
    <?> "boolean"

byte
    =   lexeme (do { m <- md ; char '\'' ; s <- character ; char '\'' ; return $ nd m $ N.LitByte s })
    <?> "byte"

caseExpression
    =   expression
    <?> "caseExpression"

caseInput
    =   do { m <- md ; c <- channel ; sQuest ; sCASE ; eol ; indent ; vs <- many1 variant ; outdent ; return $ nd m $ N.In c (nd m $ N.InCase vs) }
    <?> "caseInput"

-- This is also used for timers and ports, since the syntax is identical (and
-- the parser really can't tell at this stage which is which).
channel
    =   do { m <- md ; v <- channel' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\e s -> nd m $ N.Sub (nd m $ N.SubPlain s) e) v es }
    <?> "channel"

channel'
    =   try name
    <|> try (do { m <- md ; sLeft ; n <- channel ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ nd m $ N.Sub (nd m $ N.SubFromFor e f) n })
    <|> try (do { m <- md ; sLeft ; n <- channel ; sFROM ; e <- expression ; sRight ; return $ nd m $ N.Sub (nd m $ N.SubFrom e) n })
    <|> do { m <- md ; sLeft ; n <- channel ; sFOR ; e <- expression ; sRight ; return $ nd m $ N.Sub (nd m $ N.SubFor e) n }
    <?> "channel'"

-- FIXME should probably make CHAN INT work, since that'd be trivial...
channelType
    =   do { m <- md ; sCHAN ; sOF ; p <- protocol ; return $ nd m $ N.ChanOf p }
    <|> try (do { m <- md ; sLeft ; s <- expression ; sRight ; t <- channelType ; return $ nd m $ N.Array s t })
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
    <|> do { m <- md ; s <- try specification ; c <- occamChoice ; return $ nd m $ N.Decl s c }
    <?> "choice"

conditional
    =   do {  m <- md ; sIF ;
              do { eol ; indent ; cs <- many1 occamChoice ; outdent ; return $ nd m $ N.If cs }
              <|> do { r <- replicator ; eol ; indent ; c <- occamChoice ; outdent ; return $ nd m $ N.IfRep r c } }
    <?> "conditional"

conversion
    =   do  m <- md
            t <- dataType
            do { sROUND ; o <- operand ; return $ nd m $ N.Round t o } <|> do { sTRUNC ; o <- operand ; return $ nd m $ N.Trunc t o } <|> do { o <- operand ; return $ nd m $ N.Conv t o }
    <?> "conversion"

occamCount
    =   expression
    <?> "count"

dataType
    =   do { m <- md ; sBOOL ; return $ nd m $ N.Bool }
    <|> do { m <- md ; sBYTE ; return $ nd m $ N.Byte }
    <|> do { m <- md ; sINT ; return $ nd m $ N.Int }
    <|> do { m <- md ; sINT16 ; return $ nd m $ N.Int16 }
    <|> do { m <- md ; sINT32 ; return $ nd m $ N.Int32 }
    <|> do { m <- md ; sINT64 ; return $ nd m $ N.Int64 }
    <|> do { m <- md ; sREAL32 ; return $ nd m $ N.Real32 }
    <|> do { m <- md ; sREAL64 ; return $ nd m $ N.Real64 }
    <|> try (do { m <- md ; sLeft ; s <- expression ; sRight ; t <- dataType ; return $ nd m $ N.Array s t })
    <|> name
    <?> "data type"

declType
    =   dataType
    <|> channelType
    <|> timerType
    <|> portType

-- FIXME this originally had four lines like this, one for each of the above;
-- it might be nicer to generate a different nd m $ N.Node for each type of declaration
declaration
    =   do { m <- md ; d <- declType ; ns <- sepBy1 name sComma ; sColon ; eol ; return $ nd m $ N.Vars d ns }
    <?> "declaration"

definition
    =   do {  m <- md ; sDATA ; sTYPE ; n <- name ;
              do {sIS ; t <- dataType ; sColon ; eol ; return $ nd m $ N.DataType n t }
              <|> do { eol ; indent ; t <- structuredType ; outdent ; sColon ; eol ; return $ nd m $ N.DataType n t } }
    <|> do {  m <- md ; sPROTOCOL ; n <- name ;
              do { sIS ; p <- sequentialProtocol ; sColon ; eol ; return $ nd m $ N.Protocol n p }
              <|> do { eol ; indent ; sCASE ; eol ; indent ; ps <- many1 taggedProtocol ; outdent ; outdent ; sColon ; eol ; return $ nd m $ N.TaggedProtocol n ps } }
    <|> do { m <- md ; sPROC ; n <- name ; fs <- formalList ; eol ; indent ; p <- process ; outdent ; sColon ; eol ; return $ nd m $ N.Proc n fs p }
    <|> try (do { m <- md ; rs <- sepBy1 dataType sComma ; (n, fs) <- functionHeader ;
                  do { sIS ; el <- expressionList ; sColon ; eol ; return $ nd m $ N.FuncIs n rs fs el }
                  <|> do { eol ; indent ; vp <- valueProcess ; outdent ; sColon ; eol ; return $ nd m $ N.Func n rs fs vp } })
    <|> try (do { m <- md ; s <- specifier ; n <- name ;
                  do { sRETYPES ; v <- variable ; sColon ; eol ; return $ nd m $ N.Retypes s n v }
                  <|> do { try sRESHAPES ; v <- variable ; sColon ; eol ; return $ nd m $ N.Reshapes s n v } })
    <|> do {  m <- md ; sVAL ; s <- specifier ; n <- name ;
              do { sRETYPES ; v <- variable ; sColon ; eol ; return $ nd m $ N.ValRetypes s n v }
              <|> do { sRESHAPES ; v <- variable ; sColon ; eol ; return $ nd m $ N.ValReshapes s n v } }
    <?> "definition"

digits
    =   many1 digit
    <?> "digits"

dyadicOperator
    =   do { m <- md ; reservedOp "+" ; return $ nd m $ N.Add }
    <|> do { m <- md ; reservedOp "-" ; return $ nd m $ N.Subtr }
    <|> do { m <- md ; reservedOp "*" ; return $ nd m $ N.Mul }
    <|> do { m <- md ; reservedOp "/" ; return $ nd m $ N.Div }
    <|> do { m <- md ; reservedOp "\\" ; return $ nd m $ N.Rem }
    <|> do { m <- md ; sREM ; return $ nd m $ N.Rem }
    <|> do { m <- md ; sPLUS ; return $ nd m $ N.Plus }
    <|> do { m <- md ; sMINUS ; return $ nd m $ N.Minus }
    <|> do { m <- md ; sTIMES ; return $ nd m $ N.Times }
    <|> do { m <- md ; reservedOp "/\\" ; return $ nd m $ N.BitAnd }
    <|> do { m <- md ; reservedOp "\\/" ; return $ nd m $ N.BitOr }
    <|> do { m <- md ; reservedOp "><" ; return $ nd m $ N.BitXor }
    <|> do { m <- md ; sBITAND ; return $ nd m $ N.BitAnd }
    <|> do { m <- md ; sBITOR ; return $ nd m $ N.BitOr }
    <|> do { m <- md ; sAND ; return $ nd m $ N.And }
    <|> do { m <- md ; sOR ; return $ nd m $ N.Or }
    <|> do { m <- md ; reservedOp "=" ; return $ nd m $ N.Eq }
    <|> do { m <- md ; reservedOp "<>" ; return $ nd m $ N.NEq }
    <|> do { m <- md ; reservedOp "<" ; return $ nd m $ N.Less }
    <|> do { m <- md ; reservedOp ">" ; return $ nd m $ N.More }
    <|> do { m <- md ; reservedOp "<=" ; return $ nd m $ N.LessEq }
    <|> do { m <- md ; reservedOp ">=" ; return $ nd m $ N.MoreEq }
    <|> do { m <- md ; sAFTER ; return $ nd m $ N.After }
    <?> "dyadicOperator"

occamExponent
    =   try (do { c <- oneOf "+-" ; d <- digits ; return $ c : d })
    <?> "exponent"

expression
    =   try (do { m <- md ; o <- monadicOperator ; v <- operand ; return $ nd m $ N.MonadicOp o v })
    <|> do { m <- md ; a <- sMOSTPOS ; t <- dataType ; return $ nd m $ N.MostPos t }
    <|> do { m <- md ; a <- sMOSTNEG ; t <- dataType ; return $ nd m $ N.MostNeg t }
    <|> do { m <- md ; a <- sSIZE ; t <- dataType ; return $ nd m $ N.Size t }
    <|> try (do { m <- md ; a <- operand ; o <- dyadicOperator ; b <- operand ; return $ nd m $ N.DyadicOp o a b })
    <|> try conversion
    <|> operand
    <?> "expression"

expressionList
    =   try (do { m <- md ; n <- name ; sLeftR ; as <- sepBy expression sComma ; sRightR ; return $ nd m $ N.Call n as })
    <|> do { m <- md ; es <- sepBy1 expression sComma ; return $ nd m $ N.ExpList es }
-- XXX value process
    <?> "expressionList"

fieldName
    =   name
    <?> "fieldName"

-- This is rather different from the grammar, since I had some difficulty
-- getting Parsec to parse it as a list of lists of arguments.
formalList
    =   do { m <- md ; sLeftR ; fs <- sepBy formalArg sComma ; sRightR ; return $ markTypes m fs }
    <?> "formalList"
    where
      formalArg :: Parser (Maybe N.Node, N.Node)
      formalArg =   try (do { m <- md ; sVAL ; s <- specifier ; n <- name ; return $ (Just (nd m $ N.Val s), n) })
                <|> try (do { s <- specifier ; n <- name ; return $ (Just s, n) })
                <|> try (do { n <- name ; return $ (Nothing, n) })

      markTypes :: Meta -> [(Maybe N.Node, N.Node)] -> [N.Node]
      markTypes _ [] = []
      markTypes _ ((Nothing, _):_) = error "Formal list must start with a type"
      markTypes m ((Just ft, fn):is) = markRest m ft [fn] is

      markRest :: Meta -> N.Node -> [N.Node] -> [(Maybe N.Node, N.Node)] -> [N.Node]
      markRest m lt ns [] = [nd m $ N.Formals lt ns]
      markRest m lt ns ((Nothing, n):is) = markRest m lt (ns ++ [n]) is
      markRest m lt ns ((Just t, n):is) = (markRest m lt ns []) ++ (markRest m t [n] is)

functionHeader
    =   do { sFUNCTION ; n <- name ; fs <- formalList ; return $ (n, fs) }
    <?> "functionHeader"

guard
    =   try input
    <|> try (do { m <- md ; b <- boolean ; sAmp ; i <- input ; return $ nd m $ N.CondGuard b i })
    <|> try (do { m <- md ; b <- boolean ; sAmp ; sSKIP ; eol ; return $ nd m $ N.CondGuard b (nd m $ N.Skip) })
    <?> "guard"

guardedAlternative
    =   do { m <- md ; g <- guard ; indent ; p <- process ; outdent ; return $ nd m $ N.Guard g p }
    <?> "guardedAlternative"

guardedChoice
    =   do { m <- md ; b <- boolean ; eol ; indent ; p <- process ; outdent ; return $ nd m $ N.Choice b p }
    <?> "guardedChoice"

hexDigits
    =   do { m <- md ; d <- many1 hexDigit ; return $ nd m $ N.LitHex d }
    <?> "hexDigits"

input
    =   do  m <- md
            c <- channel
            sQuest
            (do { sCASE ; tl <- taggedList ; eol ; return $ nd m $ N.In c (nd m $ N.InTag tl) }
             <|> do { sAFTER ; e <- expression ; eol ; return $ nd m $ N.In c (nd m $ N.InAfter e) }
             <|> do { is <- sepBy1 inputItem sSemi ; eol ; return $ nd m $ N.In c (nd m $ N.InSimple is) })
    <?> "input"

inputItem
    =   try (do { m <- md ; v <- variable ; sColons ; w <- variable ; return $ nd m $ N.Counted v w })
    <|> variable
    <?> "inputItem"

integer
    =   try (do { m <- md ; d <- lexeme digits ; return $ nd m $ N.LitInt d })
    <|> do { char '#' ; d <- lexeme hexDigits ; return $ d }
    <?> "integer"

literal
    =   try real
    <|> try integer
    <|> try byte
    <|> try (do { m <- md ; v <- real ; sLeftR ; t <- dataType ; sRightR ; return $ nd m $ N.TypedLit t v })
    <|> try (do { m <- md ; v <- integer ; sLeftR ; t <- dataType ; sRightR ; return $ nd m $ N.TypedLit t v })
    <|> try (do { m <- md ; v <- byte ; sLeftR ; t <- dataType ; sRightR ; return $ nd m $ N.TypedLit t v })
    <|> try (do { m <- md ; sTRUE ; return $ nd m $ N.True })
    <|> do { m <- md ; sFALSE ; return $ nd m $ N.False }
    <?> "literal"

loop
    =   do { m <- md ; sWHILE ; b <- boolean ; eol ; indent ; p <- process ; outdent ; return $ nd m $ N.While b p }

monadicOperator
    =   do { m <- md ; reservedOp "-" ; return $ nd m $ N.MonSub }
    <|> do { m <- md ; sMINUS ; return $ nd m $ N.MonSub }
    <|> do { m <- md ; reservedOp "~" ; return $ nd m $ N.MonBitNot }
    <|> do { m <- md ; sBITNOT ; return $ nd m $ N.MonBitNot }
    <|> do { m <- md ; sNOT ; return $ nd m $ N.MonNot }
    <|> do { m <- md ; sSIZE ; return $ nd m $ N.MonSize }
    <?> "monadicOperator"

name
    =   do { m <- md ; s <- identifier ; return $ nd m $ N.Name s }
    <?> "name"

occamString
    =   lexeme (do { m <- md ; char '"' ; s <- many (noneOf "\"") ; char '"' ; return $ nd m $ N.LitString s })
    <?> "string"

operand
    =   do { m <- md ; v <- operand' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\e s -> nd m $ N.Sub (nd m $ N.SubPlain s) e) v es }
    <?> "operand"

operand'
    =   try variable
    <|> try literal
    <|> try table
    <|> try (do { sLeftR ; e <- expression ; sRightR ; return e })
-- XXX value process
    <|> try (do { m <- md ; n <- name ; sLeftR ; as <- sepBy expression sComma ; sRightR ; return $ nd m $ N.Call n as })
    <|> try (do { m <- md ; sBYTESIN ; sLeftR ; o <- operand ; sRightR ; return $ nd m $ N.BytesIn o })
    <|> try (do { m <- md ; sBYTESIN ; sLeftR ; o <- dataType ; sRightR ; return $ nd m $ N.BytesIn o })
    <|> try (do { m <- md ; sOFFSETOF ; sLeftR ; n <- name ; sComma ; f <- fieldName ; sRightR ; return $ nd m $ N.OffsetOf n f })
    <?> "operand'"

occamOption
    =   try (do { m <- md ; ces <- sepBy caseExpression sComma ; eol ; indent ; p <- process ; outdent ; return $ nd m $ N.CaseExps ces p })
    <|> try (do { m <- md ; sELSE ; eol ; indent ; p <- process ; outdent ; return $ nd m $ N.Else p })
    <|> do { m <- md ; s <- specification ; o <- occamOption ; return $ nd m $ N.Decl s o }
    <?> "option"

-- XXX This can't tell at parse time in "c ! x; y" whether x is a variable or a tag...
-- ... so this now wants "c ! CASE x" if it's a tag, to match input.
-- We can fix this with a pass later...
output
    =   do  m <- md
            c <- channel
            sBang
            (do { sCASE ; t <- tag ; sSemi ; os <- sepBy1 outputItem sSemi ; eol ; return $ nd m $ N.OutCase c t os }
             <|> do { sCASE ; t <- tag ; eol ; return $ nd m $ N.OutCase c t [] }
             <|> do { os <- sepBy1 outputItem sSemi ; eol ; return $ nd m $ N.Out c os })
    <?> "output"

outputItem
    =   try (do { m <- md ; a <- expression ; sColons ; b <- expression ; return $ nd m $ N.Counted a b })
    <|> expression
    <?> "outputItem"

parallel
    =   do { m <- md ; sPAR ; do { eol ; indent ; ps <- many1 process ; outdent ; return $ nd m $ N.Par ps } <|> do { r <- replicator ; eol ; indent ; p <- process ; outdent ; return $ nd m $ N.ParRep r p } }
    <|> do { m <- md ; sPRI ; sPAR ; do { eol ; indent ; ps <- many1 process ; outdent ; return $ nd m $ N.PriPar ps } <|> do { r <- replicator ; eol ; indent ; p <- process ; outdent ; return $ nd m $ N.PriParRep r p } }
    <|> placedpar
    <?> "parallel"

-- XXX PROCESSOR as a process isn't really legal, surely?
placedpar
    =   do { m <- md ; sPLACED ; sPAR ; do { eol ; indent ; ps <- many1 placedpar ; outdent ; return $ nd m $ N.PlacedPar ps } <|> do { r <- replicator ; eol ; indent ; p <- placedpar ; outdent ; return $ nd m $ N.PlacedParRep r p } }
    <|> do { m <- md ; sPROCESSOR ; e <- expression ; eol ; indent ; p <- process ; outdent ; return $ nd m $ N.Processor e p }
    <?> "placedpar"

portType
    =   do { m <- md ; sPORT ; sOF ; p <- protocol ; return $ nd m $ N.PortOf p }
    <|> do { m <- md ; try sLeft ; s <- try expression ; try sRight ; t <- portType ; return $ nd m $ N.Array s t }
    <?> "portType"

procInstance
    =   do { m <- md ; n <- name ; sLeftR ; as <- sepBy actual sComma ; sRightR ; eol ; return $ nd m $ N.ProcCall n as }
    <?> "procInstance"

process
    =   try assignment
    <|> try input
    <|> try output
    <|> do { m <- md ; sSKIP ; eol ; return $ nd m $ N.Skip }
    <|> do { m <- md ; sSTOP ; eol ; return $ nd m $ N.Stop }
    <|> occamSequence
    <|> conditional
    <|> selection
    <|> loop
    <|> try parallel
    <|> alternation
    <|> try caseInput
    <|> try procInstance
    <|> do { m <- md ; sMainMarker ; eol ; return $ nd m $ N.MainProcess }
    <|> do { m <- md ; a <- allocation ; p <- process ; return $ nd m $ N.Decl a p }
    <|> do { m <- md ; s <- specification ; p <- process ; return $ nd m $ N.Decl s p }
    <?> "process"

protocol
    =   try name
    <|> simpleProtocol
    <?> "protocol"

real
    =   try (do { m <- md ; l <- digits ; char '.' ; r <- digits ; char 'e' ; e <- lexeme occamExponent ; return $ nd m $ N.LitReal (l ++ "." ++ r ++ "e" ++ e) })
    <|> do { m <- md ; l <- digits ; char '.' ; r <- lexeme digits ; return $ nd m $ N.LitReal (l ++ "." ++ r) }
    <?> "real"

replicator
    =   do { m <- md ; n <- name ; sEq ; b <- base ; sFOR ; c <- occamCount ; return $ nd m $ N.For n b c }
    <?> "replicator"

selection
    =   do { m <- md ; sCASE ; s <- selector ; eol ; indent ; os <- many1 occamOption ; outdent ; return $ nd m $ N.Case s os }
    <?> "selection"

selector
    =   expression
    <?> "selector"

occamSequence
    =   do  m <- md
            sSEQ
            (do { eol ; indent ; ps <- many1 process ; outdent ; return $ nd m $ N.Seq ps }
             <|> do { r <- replicator ; eol ; indent ; p <- process ; outdent ; return $ nd m $ N.SeqRep r p })
    <?> "sequence"

sequentialProtocol
    =   do { l <- try $ sepBy1 simpleProtocol sSemi ; return $ l }
    <?> "sequentialProtocol"

simpleProtocol
    =   try (do { m <- md ; l <- dataType ; sColons ; sLeft ; sRight ; r <- dataType ; return $ nd m $ N.Counted l r })
    <|> dataType
    <|> do { m <- md ; sANY ; return $ nd m $ N.Any }
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
    <|> try (do { m <- md ; sLeft ; sRight ; s <- specifier ; return $ nd m $ N.ArrayUnsized s })
    <|> do { m <- md ; sLeft ; e <- expression ; sRight ; s <- specifier ; return $ nd m $ N.Array e s }
    <?> "specifier"

structuredType
    =   try (do { m <- md ; sRECORD ; eol ; indent ; fs <- many1 structuredTypeField ; outdent ; return $ nd m $ N.Record fs })
    <|> do { m <- md ; sPACKED ; sRECORD ; eol ; indent ; fs <- many1 structuredTypeField ; outdent ; return $ nd m $ N.PackedRecord fs }
    <?> "structuredType"

-- FIXME this should use the same type-folding code as proc/func definitions
structuredTypeField
    =   do { m <- md ; t <- dataType ; fs <- many1 fieldName ; sColon ; eol ; return $ nd m $ N.Fields t fs }
    <?> "structuredTypeField"

-- i.e. array literal
table
    =   do { m <- md ; v <- table' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\e s -> nd m $ N.Sub (nd m $ N.SubPlain s) e) v es }
    <?> "table"

table'
    =   try occamString
    <|> try (do { m <- md ; s <- occamString ; sLeftR ; n <- name ; sRightR ; return $ nd m $ N.TypedLit n s })
    <|> do {  sLeft ;
              try (do { m <- md ; es <- sepBy1 expression sComma ; sRight ; return $ nd m $ N.LitArray es })
              <|> try (do { m <- md ; n <- table ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ nd m $ N.Sub (nd m $ N.SubFromFor e f) n })
              <|> try (do { m <- md ; n <- table ; sFROM ; e <- expression ; sRight ; return $ nd m $ N.Sub (nd m $ N.SubFrom e) n })
              <|> do { m <- md ; n <- table ; sFOR ; e <- expression ; sRight ; return $ nd m $ N.Sub (nd m $ N.SubFor e) n } }
    <?> "table'"

tag
    =   name
    <?> "tag"

taggedList
    =   try (do { m <- md ; t <- tag ; sSemi ; is <- sepBy1 inputItem sSemi ; return $ nd m $ N.Tag t is })
    <|> do { m <- md ; t <- tag ; return $ nd m $ N.Tag t [] }
    <?> "taggedList"

taggedProtocol
    =   try (do { m <- md ; t <- tag ; eol ; return $ nd m $ N.Tag t [] })
    <|> try (do { m <- md ; t <- tag ; sSemi ; sp <- sequentialProtocol ; eol ; return $ nd m $ N.Tag t sp })

timerType
    =   do { m <- md ; sTIMER ; return $ nd m $ N.Timer }
    <|> do { m <- md ; try sLeft ; s <- try expression ; try sRight ; t <- timerType ; return $ nd m $ N.Array s t }
    <?> "timerType"

valueProcess
    =   try (do { m <- md ; sVALOF ; eol ; indent ; p <- process ; sRESULT ; el <- expressionList ; eol ; outdent ; return $ nd m $ N.ValOf p el })
    <|> do { m <- md ; s <- specification ; v <- valueProcess ; return $ nd m $ N.Decl s v }

variable
    =   do { m <- md ; v <- variable' ; es <- many (do { sLeft ; e <- expression ; sRight ; return e }) ; return $ foldl (\e s -> nd m $ N.Sub (nd m $ N.SubPlain s) e) v es }
    <?> "variable"

variable'
    =   try name
    <|> try (do { m <- md ; sLeft ; n <- variable ; sFROM ; e <- expression ; sFOR ; f <- expression ; sRight ; return $ nd m $ N.Sub (nd m $ N.SubFromFor e f) n })
    <|> try (do { m <- md ; sLeft ; n <- variable ; sFROM ; e <- expression ; sRight ; return $ nd m $ N.Sub (nd m $ N.SubFrom e) n })
    <|> do { m <- md ; sLeft ; n <- variable ; sFOR ; e <- expression ; sRight ; return $ nd m $ N.Sub (nd m $ N.SubFor e) n }
    <?> "variable'"

variableList
    =   do { vs <- sepBy1 variable sComma ; return $ vs }
    <?> "variableList"

variant
    =   try (do { m <- md ; t <- taggedList ; eol ; indent ; p <- process ; outdent ; return $ nd m $ N.Variant t p })
    <|> do { m <- md ; s <- specification ; v <- variant ; return $ nd m $ N.Decl s v }
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
            stripped' = stripComment s
            stripped = if stripIndent stripped' == "" then "" else (stripped' ++ "@")
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

parseSource :: String -> String -> N.Node
parseSource prep sourceFileName
  = case (parse sourceFile sourceFileName prep) of
      Left err -> error ("Parsing error: " ++ (show err))
      Right defs -> defs

