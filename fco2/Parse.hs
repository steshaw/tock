-- Parse occam code

module Parse (readSource, parseSource) where

import Data.List
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language (emptyDef)
import qualified IO
import Numeric (readHex)

import qualified AST as A
import Metadata

-- FIXME: Restructure this by construct (i.e. group all the IF stuff together), and add folds.
-- FIXME: We should be using a custom type which handles errors and state tracking, not Parser directly.

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

md :: Parser Meta
md = do
  pos <- getPosition
  return $ [SourcePos (sourceName pos) (sourceLine pos) (sourceColumn pos)]

maybeSubscripted :: String -> Parser a -> (Meta -> A.Subscript -> a -> a) -> Parser a
maybeSubscripted prodName inner subscripter
    =   do m <- md
           v <- inner
           es <- many (do { sLeft; e <- expression; sRight; return e })
           return $ foldl (\e s -> subscripter m (A.Subscript m s) e) v es
    <?> prodName

maybeSliced :: Parser a -> (Meta -> A.Subscript -> a -> a) -> Parser a
maybeSliced inner subscripter
    =   do m <- md
           sLeft
           v <- inner
           (try (do { sFROM; e <- expression; sFOR; f <- expression; sRight; return $ subscripter m (A.SubscriptFromFor m e f) v })
            <|> do { sFROM; e <- expression; sRight; return $ subscripter m (A.SubscriptFrom m e) v }
            <|> do { sFOR; e <- expression; sRight; return $ subscripter m (A.SubscriptFor m e) v })

handleSpecs :: Parser [A.Specification] -> Parser a -> (Meta -> A.Specification -> a -> a) -> Parser a
handleSpecs specs inner specMarker
    =   do m <- md
           ss <- specs
           v <- inner
           return $ foldl (\e s -> specMarker m s e) v ss

-- -------------------------------------------------------------

-- These productions are based on the syntax in the occam2.1 manual.

-- The way productions should work is that each production should only consume input if it's sure that it's unambiguous.

abbreviation :: Parser A.Specification
abbreviation
    =   try (do { m <- md; n <- name; sIS; v <- variable; sColon; eol; return (n, A.Is m A.Infer v) })
    <|> try (do { m <- md; s <- specifier; n <- name; sIS; v <- variable; sColon; eol; return (n, A.Is m s v) })
    <|> do { m <- md; sVAL ;
              try (do { n <- name; sIS; e <- expression; sColon; eol; return (n, A.ValIs m A.Infer e) })
              <|> do { s <- specifier; n <- name; sIS; e <- expression; sColon; eol; return (n, A.ValIs m s e) } }
    <?> "abbreviation"

actual :: Parser A.Actual
actual
    =   try (do { e <- expression; return $ A.ActualExpression e })
    <|> try (do { c <- channel; return $ A.ActualChannel c })
    <?> "actual"

allocation :: Parser [A.Specification]
allocation
    =   do { m <- md; sPLACE; n <- name; sAT; e <- expression; sColon; eol; return [(n, A.Place m e)] }
    <?> "allocation"

altProcess :: Parser A.Process
altProcess
    =   do m <- md
           (isPri, a) <- alternation
           return $ A.Alt m isPri a
    <?> "altProcess"

altKeyword :: Parser Bool
altKeyword
    =   do { sALT; return False }
    -- FIXME Can this be relaxed to just wrap sPRI in "try"?
    <|> try (do { sPRI; sALT; return True })
    <?> "altKeyword"

alternation :: Parser (Bool, A.Structured)
alternation
    =   do {  m <- md; isPri <- altKeyword ;
              do { eol; indent; as <- many1 alternative; outdent; return (isPri, A.Several m as) }
              <|> do { r <- replicator; eol; indent; a <- alternative; outdent; return (isPri, A.Rep m r a) } }
    <?> "alternation"

-- The reason the CASE guards end up here is because they have to be handled
-- specially: you can't tell until parsing the guts of the CASE what the processes
-- are.
alternative :: Parser A.Structured
alternative
    =   guardedAlternative
    -- FIXME: Check we don't have PRI ALT inside ALT.
    <|> do { (isPri, a) <- alternation; return a }
    <|> try (do m <- md
                b <- boolean
                sAmp
                c <- channel
                sQuest
                sCASE
                eol
                indent
                vs <- many1 variant
                outdent
                return $ A.OnlyA m (A.AlternativeCond m b c (A.InputCase m $ A.Several m vs) (A.Skip m)))
    <|> try (do m <- md
                c <- channel
                sQuest
                sCASE
                eol
                indent
                vs <- many1 variant
                outdent
                return $ A.OnlyA m (A.Alternative m c (A.InputCase m $ A.Several m vs) (A.Skip m)))
    <|> handleSpecs specification alternative A.Spec
    <?> "alternative"

assignment :: Parser A.Process
assignment
    =   do { m <- md; vs <- variableList; sAssign; es <- expressionList; eol; return $ A.Assign m vs es }
    <?> "assignment"

repBase :: Parser A.Expression
repBase
    -- FIXME: Check the type is INT (and probably collapse all of these into "intExpression")
    =   expression
    <?> "repBase"

boolean :: Parser A.Expression
boolean
    -- FIXME: Check the type is BOOL
    =   expression
    <?> "boolean"

byte :: Parser A.LiteralRepr
byte
    =   lexeme (do { m <- md; char '\''; s <- character; char '\''; return $ A.ByteLiteral m s })
    <?> "byte"

caseExpression :: Parser A.Expression
caseExpression
    -- FIXME: Check the type is something that CASE can deal with
    =   expression
    <?> "caseExpression"

caseInput :: Parser A.Process
caseInput
    =   do { m <- md; c <- channel; sQuest; sCASE; eol; indent; vs <- many1 variant; outdent; return $ A.Input m c (A.InputCase m (A.Several m vs)) }
    <?> "caseInput"

-- This is also used for timers and ports, since the syntax is identical (and
-- the parser really can't tell at this stage which is which).
-- FIXME: The above isn't true any more -- this should be a more general thing, with a typecheck.
-- FIXME: This should pick up metadata for each subscript expression.
channel :: Parser A.Channel
channel
    =   maybeSubscripted "channel" channel' A.SubscriptedChannel
    <?> "channel"

channel' :: Parser A.Channel
channel'
    =   try (do { m <- md; n <- name; return $ A.Channel m n })
    <|> try (maybeSliced channel A.SubscriptedChannel)
    <?> "channel'"

-- FIXME should probably make CHAN INT work, since that'd be trivial...
channelType :: Parser A.Type
channelType
    =   do { sCHAN; sOF; p <- protocol; return $ A.Chan p }
    <|> try (do { sLeft; s <- expression; sRight; t <- channelType; return $ A.Array s t })
    <?> "channelType"

character :: Parser String
character
    =   try (do { char '*' ;
                  do char '#'
                     a <- hexDigit
                     b <- hexDigit
                     return $ ['*', '#', a, b]
                  -- FIXME: Handle *\n, which is just a line continuation?
                  <|> do { c <- anyChar; return ['*', c] } })
    <|> do { c <- anyChar; return [c] }
    <?> "character"

ifProcess :: Parser A.Process
ifProcess
    =   do m <- md
           c <- conditional
           return $ A.If m c
    <?> "ifProcess"

caseChoice :: Parser A.Structured
caseChoice
    =   guardedChoice
    <|> conditional
    <|> handleSpecs specification caseChoice A.Spec
    <?> "choice"

conditional :: Parser A.Structured
conditional
    =   do {  m <- md; sIF ;
              do { eol; indent; cs <- many1 caseChoice; outdent; return $ A.Several m cs }
              <|> do { r <- replicator; eol; indent; c <- caseChoice; outdent; return $ A.Rep m r c } }
    <?> "conditional"

conversionMode :: Parser (A.ConversionMode, A.Expression)
conversionMode
    =   do { sROUND; o <- operand; return (A.Round, o) }
    <|> do { sTRUNC; o <- operand; return (A.Trunc, o) }
    -- This uses operandNotTable to resolve the "x[y]" ambiguity.
    <|> do { o <- operandNotTable; return (A.DefaultConversion, o) }
    <?> "conversionMode"

conversion :: Parser A.Expression
conversion
    =   try (do m <- md
                t <- dataType
                (c, o) <- conversionMode
                return $ A.Conversion m c t o)
    <?> "conversion"

repCount :: Parser A.Expression
repCount
    -- FIXME: Check type
    =   expression
    <?> "repCount"

dataType :: Parser A.Type
dataType
    =   do { sBOOL; return A.Bool }
    <|> do { sBYTE; return A.Byte }
    <|> do { sINT; return A.Int }
    <|> do { sINT16; return A.Int16 }
    <|> do { sINT32; return A.Int32 }
    <|> do { sINT64; return A.Int64 }
    <|> do { sREAL32; return A.Real32 }
    <|> do { sREAL64; return A.Real64 }
    <|> try (do { sLeft; s <- expression; sRight; t <- dataType; return $ A.Array s t })
    <|> do { n <- name; return $ A.UserType n }
    <?> "dataType"

declType :: Parser A.Type
declType
    =   dataType
    <|> channelType
    <|> timerType
    <|> portType
    <?> "declType"

-- FIXME this originally had four lines like this, one for each of the above;
-- it will need to register them as different types of name
declaration :: Parser ([A.Name], A.SpecType)
declaration
    =   do { m <- md; d <- declType; ns <- sepBy1 name sComma; sColon; eol; return (ns, A.Declaration m d) }
    <?> "declaration"

definition :: Parser A.Specification
definition
    =   do {  m <- md; sDATA; sTYPE; n <- name ;
              do {sIS; t <- dataType; sColon; eol; return (n, A.DataType m t) }
              <|> do { eol; indent; rec <- structuredType; outdent; sColon; eol; return (n, rec) } }
    <|> do {  m <- md; sPROTOCOL; n <- name ;
              do { sIS; p <- sequentialProtocol; sColon; eol; return (n, A.Protocol m p) }
              <|> do { eol; indent; sCASE; eol; indent; ps <- many1 taggedProtocol; outdent; outdent; sColon; eol; return (n, A.ProtocolCase m ps) } }
    <|> do { m <- md; sPROC; n <- name; fs <- formalList; eol; indent; p <- process; outdent; sColon; eol; return (n, A.Proc m fs p) }
    <|> try (do { m <- md; rs <- sepBy1 dataType sComma; (n, fs) <- functionHeader ;
                  do { sIS; el <- expressionList; sColon; eol; return (n, A.Function m rs fs (A.ValOf m (A.Skip m) el)) }
                  <|> do { eol; indent; vp <- valueProcess; outdent; sColon; eol; return (n, A.Function m rs fs vp) } })
    <|> try (do { m <- md; s <- specifier; n <- name ;
                  do { sRETYPES; v <- variable; sColon; eol; return (n, A.Retypes m s v) }
                  <|> do { try sRESHAPES; v <- variable; sColon; eol; return (n, A.Reshapes m s v) } })
    <|> do {  m <- md; sVAL; s <- specifier; n <- name ;
              do { sRETYPES; v <- variable; sColon; eol; return (n, A.ValRetypes m s v) }
              <|> do { sRESHAPES; v <- variable; sColon; eol; return (n, A.ValReshapes m s v) } }
    <?> "definition"

digits :: Parser String
digits
    =   many1 digit
    <?> "digits"

dyadicOperator :: Parser A.DyadicOp
dyadicOperator
    =   do { reservedOp "+"; return A.Add }
    <|> do { reservedOp "-"; return A.Subtr }
    <|> do { reservedOp "*"; return A.Mul }
    <|> do { reservedOp "/"; return A.Div }
    <|> do { reservedOp "\\"; return A.Rem }
    <|> do { sREM; return A.Rem }
    <|> do { sPLUS; return A.Plus }
    <|> do { sMINUS; return A.Minus }
    <|> do { sTIMES; return A.Times }
    <|> do { reservedOp "/\\" <|> sBITAND; return A.BitAnd }
    <|> do { reservedOp "\\/" <|> sBITOR; return A.BitOr }
    <|> do { reservedOp "><"; return A.BitXor }
    <|> do { sAND; return A.And }
    <|> do { sOR; return A.Or }
    <|> do { reservedOp "="; return A.Eq }
    <|> do { reservedOp "<>"; return A.NotEq }
    <|> do { reservedOp "<"; return A.Less }
    <|> do { reservedOp ">"; return A.More }
    <|> do { reservedOp "<="; return A.LessEq }
    <|> do { reservedOp ">="; return A.MoreEq }
    <|> do { sAFTER; return A.After }
    <?> "dyadicOperator"

expression :: Parser A.Expression
expression
    =   try (do { m <- md; o <- monadicOperator; v <- operand; return $ A.Monadic m o v })
    <|> do { m <- md; sMOSTPOS; t <- dataType; return $ A.MostPos m t }
    <|> do { m <- md; sMOSTNEG; t <- dataType; return $ A.MostNeg m t }
    <|> do { m <- md; sSIZE; t <- dataType; return $ A.Size m t }
    <|> do { m <- md; sTRUE; return $ A.True m }
    <|> do { m <- md; sFALSE; return $ A.False m }
    <|> try (do { m <- md; l <- operand; o <- dyadicOperator; r <- operand; return $ A.Dyadic m o l r })
    <|> try conversion
    <|> operand
    <?> "expression"

expressionList :: Parser A.ExpressionList
expressionList
    =   try (do { m <- md; n <- name; sLeftR; as <- sepBy expression sComma; sRightR; return $ A.FunctionCallList m n as })
    <|> do { m <- md; es <- sepBy1 expression sComma; return $ A.ExpressionList m es }
-- XXX: Value processes are not supported (because nobody uses them and they're hard to parse)
    <?> "expressionList"

fieldName :: Parser A.Tag
fieldName = tag

-- This is rather different from the grammar, since I had some difficulty
-- getting Parsec to parse it as a list of lists of arguments.
formalList :: Parser A.Formals
formalList
    =   do { m <- md; sLeftR; fs <- sepBy formalArg sComma; sRightR; return $ markTypes m fs }
    <?> "formalList"
    where
      formalArg :: Parser (Maybe A.Type, A.Name)
      formalArg =   try (do { sVAL; s <- specifier; n <- name; return $ (Just (A.Val s), n) })
                <|> try (do { s <- specifier; n <- name; return $ (Just s, n) })
                <|> try (do { n <- name; return $ (Nothing, n) })

      markTypes :: Meta -> [(Maybe A.Type, A.Name)] -> A.Formals
      markTypes _ [] = []
      markTypes _ ((Nothing, _):_) = error "Formal list must start with a type"
      markTypes m ((Just ft, fn):is) = markRest m ft [fn] is

      markRest :: Meta -> A.Type -> [A.Name] -> [(Maybe A.Type, A.Name)] -> A.Formals
      markRest m lt ns [] = [(lt, n) | n <- ns]
      markRest m lt ns ((Nothing, n):is) = markRest m lt (ns ++ [n]) is
      markRest m lt ns ((Just t, n):is) = (markRest m lt ns []) ++ (markRest m t [n] is)

functionHeader :: Parser (A.Name, A.Formals)
functionHeader
    =   do { sFUNCTION; n <- name; fs <- formalList; return $ (n, fs) }
    <?> "functionHeader"

guard :: Parser (A.Process -> A.Alternative)
guard
    =   try (do { m <- md; (c, im) <- input; return $ A.Alternative m c im })
    <|> try (do { m <- md; b <- boolean; sAmp; (c, im) <- input; return $ A.AlternativeCond m b c im })
    <|> try (do { m <- md; b <- boolean; sAmp; sSKIP; eol; return $ A.AlternativeSkip m b })
    <?> "guard"

guardedAlternative :: Parser A.Structured
guardedAlternative
    =   do m <- md
           makeAlt <- guard
           indent
           p <- process
           outdent
           return $ A.OnlyA m (makeAlt p)
    <?> "guardedAlternative"

guardedChoice :: Parser A.Structured
guardedChoice
    =   do m <- md
           b <- boolean
           eol
           indent
           p <- process
           outdent
           return $ A.OnlyC m (A.Choice m b p)
    <?> "guardedChoice"

inputProcess :: Parser A.Process
inputProcess
    =   do m <- md
           (c, i) <- input
           return $ A.Input m c i

input :: Parser (A.Channel, A.InputMode)
input
    =   do  m <- md
            c <- channel
            sQuest
            (do { sCASE; tl <- taggedList; eol; return (c, A.InputCase m (A.OnlyV m (tl (A.Skip m)))) }
             <|> do { sAFTER; e <- expression; eol; return (c, A.InputAfter m e) }
             <|> do { is <- sepBy1 inputItem sSemi; eol; return (c, A.InputSimple m is) })
    <?> "input"

inputItem :: Parser A.InputItem
inputItem
    =   try (do { m <- md; v <- variable; sColons; w <- variable; return $ A.InCounted m v w })
    <|> do { m <- md; v <- variable; return $ A.InVariable m v }
    <?> "inputItem"

integer :: Parser A.LiteralRepr
integer
    =   try (do { m <- md; d <- lexeme digits; return $ A.IntLiteral m d })
    <|> do { m <- md; char '#'; d <- many1 hexDigit; return $ A.HexLiteral m d }
    <?> "integer"

literal :: Parser A.Literal
literal
    =   try (do { m <- md; v <- real; sLeftR; t <- dataType; sRightR; return $ A.Literal m t v })
    <|> try (do { m <- md; v <- integer; sLeftR; t <- dataType; sRightR; return $ A.Literal m t v })
    <|> try (do { m <- md; v <- byte; sLeftR; t <- dataType; sRightR; return $ A.Literal m t v })
    <|> try (do { m <- md; r <- real; return $ A.Literal m A.Infer r })
    <|> try (do { m <- md; r <- integer; return $ A.Literal m A.Infer r })
    <|> try (do { m <- md; r <- byte; return $ A.Literal m A.Infer r })
    <?> "literal"

whileProcess :: Parser A.Process
whileProcess
    =   do m <- md
           sWHILE
           b <- boolean
           eol
           indent
           p <- process
           outdent
           return $ A.While m b p
    <?> "whileProcess"

monadicOperator :: Parser A.MonadicOp
monadicOperator
    =   do { reservedOp "-" <|> sMINUS; return A.MonadicSubtr }
    <|> do { reservedOp "~" <|> sBITNOT; return A.MonadicBitNot }
    <|> do { sNOT; return A.MonadicNot }
    <|> do { sSIZE; return A.MonadicSize }
    <?> "monadicOperator"

name :: Parser A.Name
name
    =   do m <- md
           s <- identifier
           return $ A.Name m s
    <?> "name"

stringLiteral :: Parser A.LiteralRepr
stringLiteral
    =   lexeme (do { m <- md; char '"'; cs <- many character; char '"'; return $ A.StringLiteral m (concat cs) })
    <?> "string"

operandNotTable :: Parser A.Expression
operandNotTable
    = maybeSubscripted "operandNotTable" operandNotTable' A.SubscriptedExpr

operand :: Parser A.Expression
operand
    = maybeSubscripted "operand" operand' A.SubscriptedExpr

operandNotTable' :: Parser A.Expression
operandNotTable'
    =   try (do { m <- md; v <- variable; return $ A.ExprVariable m v })
    <|> try (do { m <- md; l <- literal; return $ A.ExprLiteral m l })
    <|> try (do { sLeftR; e <- expression; sRightR; return e })
-- XXX value process
    <|> try (do { m <- md; n <- name; sLeftR; as <- sepBy expression sComma; sRightR; return $ A.FunctionCall m n as })
    <|> try (do { m <- md; sBYTESIN; sLeftR; o <- operand; sRightR; return $ A.BytesInExpr m o })
    <|> try (do { m <- md; sBYTESIN; sLeftR; t <- dataType; sRightR; return $ A.BytesInType m t })
    <|> try (do { m <- md; sOFFSETOF; sLeftR; t <- dataType; sComma; f <- fieldName; sRightR; return $ A.OffsetOf m t f })
    <?> "operandNotTable'"

operand' :: Parser A.Expression
operand'
    =   try (do { m <- md; l <- table; return $ A.ExprLiteral m l })
    <|> operandNotTable'
    <?> "operand'"

caseOption :: Parser A.Structured
caseOption
    =   try (do { m <- md; ces <- sepBy caseExpression sComma; eol; indent; p <- process; outdent; return $ A.OnlyO m (A.Option m ces p) })
    <|> try (do { m <- md; sELSE; eol; indent; p <- process; outdent; return $ A.OnlyO m (A.Else m p) })
    <|> handleSpecs specification caseOption A.Spec
    <?> "option"

-- XXX This can't tell at parse time in "c ! x; y" whether x is a variable or a tag...
-- ... so this now wants "c ! CASE x" if it's a tag, to match input.
-- FIXME: We'll be able to deal with this once state is added.
output :: Parser A.Process
output
    =   do  m <- md
            c <- channel
            sBang
            (do { sCASE; t <- tag; sSemi; os <- sepBy1 outputItem sSemi; eol; return $ A.OutputCase m c t os }
             <|> do { sCASE; t <- tag; eol; return $ A.OutputCase m c t [] }
             <|> do { os <- sepBy1 outputItem sSemi; eol; return $ A.Output m c os })
    <?> "output"

outputItem :: Parser A.OutputItem
outputItem
    =   try (do { m <- md; a <- expression; sColons; b <- expression; return $ A.OutCounted m a b })
    <|> do { m <- md; e <- expression; return $ A.OutExpression m e }
    <?> "outputItem"

parKeyword :: Parser A.ParMode
parKeyword
    =   do { sPAR; return A.PlainPar }
    <|> try (do { sPRI; sPAR; return A.PriPar })
    <?> "parKeyword"

parallel :: Parser A.Process
parallel
    =   do m <- md
           isPri <- parKeyword
           (do { eol; indent; ps <- many1 process; outdent; return $ A.Par m isPri ps }
            <|> do { r <- replicator; eol; indent; p <- process; outdent; return $ A.ParRep m isPri r p })
    <|> placedpar
    <?> "parallel"

-- XXX PROCESSOR as a process isn't really legal, surely?
placedpar :: Parser A.Process
placedpar
    =   do m <- md
           sPLACED
           sPAR
           (do { eol; indent; ps <- many1 placedpar; outdent; return $ A.Par m A.PlacedPar ps  }
            <|> do { r <- replicator; eol; indent; p <- placedpar; outdent; return $ A.ParRep m A.PlacedPar r p })
    <|> do { m <- md; sPROCESSOR; e <- expression; eol; indent; p <- process; outdent; return $ A.Processor m e p }
    <?> "placedpar"

portType :: Parser A.Type
portType
    =   do { sPORT; sOF; p <- dataType; return $ A.Port p }
    <|> do { m <- md; try sLeft; s <- try expression; try sRight; t <- portType; return $ A.Array s t }
    <?> "portType"

procInstance :: Parser A.Process
procInstance
    =   do { m <- md; n <- name; sLeftR; as <- sepBy actual sComma; sRightR; eol; return $ A.ProcCall m n as }
    <?> "procInstance"

process :: Parser A.Process
process
    =   try assignment
    <|> try inputProcess
    <|> try output
    <|> do { m <- md; sSKIP; eol; return $ A.Skip m }
    <|> do { m <- md; sSTOP; eol; return $ A.Stop m }
    <|> seqProcess
    <|> ifProcess
    <|> caseProcess
    <|> whileProcess
    <|> try parallel
    <|> altProcess
    <|> try caseInput
    <|> try procInstance
    <|> do { m <- md; sMainMarker; eol; return $ A.Main m }
    <|> handleSpecs (allocation <|> specification) process A.ProcSpec
    <?> "process"

protocol :: Parser A.Type
protocol
-- FIXME The ordered syntax has "name" in here too.
-- We should really have protocolName, variableName, functionName, tagName, etc. which operate in different namespaces.
    =   simpleProtocol
    <?> "protocol"

occamExponent :: Parser String
occamExponent
    =   try (do { c <- oneOf "+-"; d <- digits; return $ c : d })
    <?> "exponent"

real :: Parser A.LiteralRepr
real
    =   try (do m <- md
                l <- digits
                char '.'
                r <- digits
                char 'e'
                e <- lexeme occamExponent
                return $ A.RealLiteral m (l ++ "." ++ r ++ "e" ++ e))
    <|> do m <- md
           l <- digits
           char '.'
           r <- lexeme digits
           return $ A.RealLiteral m (l ++ "." ++ r)
    <?> "real"

replicator :: Parser A.Replicator
replicator
    =   do { m <- md; n <- name; sEq; b <- repBase; sFOR; c <- repCount; return $ A.For m n b c }
    <?> "replicator"

caseProcess :: Parser A.Process
caseProcess
    =   do { m <- md; sCASE; s <- selector; eol; indent; os <- many1 caseOption; outdent; return $ A.Case m s (A.Several m os) }
    <?> "caseProcess"

selector :: Parser A.Expression
selector
-- FIXME Should constrain to things that can be CASEd over.
    =   expression
    <?> "selector"

seqProcess :: Parser A.Process
seqProcess
    =   do  m <- md
            sSEQ
            (do { eol; indent; ps <- many1 process; outdent; return $ A.Seq m ps }
             <|> do { r <- replicator; eol; indent; p <- process; outdent; return $ A.SeqRep m r p })
    <?> "seqProcess"

sequentialProtocol :: Parser [A.Type]
sequentialProtocol
    =   do { l <- try $ sepBy1 simpleProtocol sSemi; return l }
    <?> "sequentialProtocol"

simpleProtocol :: Parser A.Type
simpleProtocol
    =   try (do { l <- dataType; sColons; sLeft; sRight; r <- dataType; return $ A.Counted l r })
    <|> dataType
    <|> do { sANY; return $ A.Any }
    <?> "simpleProtocol"

specification :: Parser [A.Specification]
specification
    =   try (do { (ns, d) <- declaration; return [(n, d) | n <- ns] })
    <|> try (do { a <- abbreviation; return [a] })
    <|> do { d <- definition; return [d] }
    <?> "specification"

specifier :: Parser A.Type
specifier
    =   try dataType
    <|> try channelType
    <|> try timerType
    <|> try portType
    <|> try (do { sLeft; sRight; s <- specifier; return $ A.ArrayUnsized s })
    <|> do { sLeft; e <- expression; sRight; s <- specifier; return $ A.Array e s }
    <?> "specifier"

recordKeyword :: Parser Bool
recordKeyword
    =   do { sPACKED; sRECORD; return True }
    <|> do { sRECORD; return False }
    <?> "recordKeyword"

structuredType :: Parser A.SpecType
structuredType
    =   do m <- md
           isPacked <- recordKeyword
           eol
           indent
           fs <- many1 structuredTypeField
           outdent
           return $ A.DataTypeRecord m isPacked (concat fs)
    <?> "structuredType"

-- FIXME this should use the same type-folding code as proc/func definitions
structuredTypeField :: Parser [(A.Type, A.Tag)]
structuredTypeField
    =   do { t <- dataType; fs <- many1 fieldName; sColon; eol; return [(t, f) | f <- fs]  }
    <?> "structuredTypeField"

-- i.e. array literal
table :: Parser A.Literal
table
    = maybeSubscripted "table" table' A.SubscriptedLiteral

table' :: Parser A.Literal
table'
    =   try (do { m <- md; s <- stringLiteral; sLeftR; t <- dataType; sRightR; return $ A.Literal m t s })
    <|> try (do { m <- md; s <- stringLiteral; return $ A.Literal m A.Infer s })
    <|> try (do { m <- md; sLeft; es <- sepBy1 expression sComma; sRight; return $ A.Literal m A.Infer (A.ArrayLiteral m es) })
    <|> try (maybeSliced table A.SubscriptedLiteral)
    <?> "table'"

-- FIXME Should be another type of name...
tag :: Parser A.Tag
tag
    =   do m <- md
           s <- identifier
           return $ A.Tag m s
    <?> "tag"

taggedList :: Parser (A.Process -> A.Variant)
taggedList
    =   try (do { m <- md; t <- tag; sSemi; is <- sepBy1 inputItem sSemi; return $ A.Variant m t is })
    <|> do { m <- md; t <- tag; return $ A.Variant m t [] }
    <?> "taggedList"

taggedProtocol :: Parser (A.Tag, [A.Type])
taggedProtocol
    =   try (do { t <- tag; eol; return (t, [])  })
    <|> try (do { t <- tag; sSemi; sp <- sequentialProtocol; eol; return (t, sp) })
    <?> "taggedProtocol"

timerType :: Parser A.Type
timerType
    =   do { sTIMER; return $ A.Timer }
    <|> try (do { sLeft; s <- expression; sRight; t <- timerType; return $ A.Array s t })
    <?> "timerType"

valueProcess :: Parser A.ValueProcess
valueProcess
    =   try (do { m <- md; sVALOF; eol; indent; p <- process; sRESULT; el <- expressionList; eol; outdent; return $ A.ValOf m p el })
    <|> handleSpecs specification valueProcess A.ValOfSpec

variable :: Parser A.Variable
variable
    = maybeSubscripted "variable" variable' A.SubscriptedVariable

variable' :: Parser A.Variable
variable'
    =   try (do { m <- md; n <- name; return $ A.Variable m n })
    <|> try (maybeSliced variable A.SubscriptedVariable)
    <?> "variable'"

variableList :: Parser [A.Variable]
variableList
    =   do { vs <- sepBy1 variable sComma; return $ vs }
    <?> "variableList"

variant :: Parser A.Structured
variant
    =   try (do { m <- md; tl <- taggedList; eol; indent; p <- process; outdent; return $ A.OnlyV m (tl p) })
    <|> handleSpecs specification variant A.Spec
    <?> "variant"

-- -------------------------------------------------------------

-- This is only really true once we've tacked a process onto the bottom; a
-- source file is really a series of specifications, but the later ones need to
-- have the earlier ones in scope, so we can't parse them separately.

sourceFile = do { whiteSpace; process }

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

parseSource :: String -> String -> A.Process
parseSource prep sourceFileName
  = case (parse sourceFile sourceFileName prep) of
      Left err -> error ("Parsing error: " ++ (show err))
      Right defs -> defs

