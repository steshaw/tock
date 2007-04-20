-- | Parse occam code into an AST.
module Parse where

-- FIXME: Need to:
-- - insert type checks
-- - remove as many trys as possible; every production should consume input
--   when it's unambiguous

import Control.Monad.State (StateT, execStateT, liftIO, modify, get)
import Data.List
import Data.Maybe
import qualified IO
import Numeric (readHex)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language (emptyDef)
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.Regex

import qualified AST as A
import Errors
import EvalConstants
import Indentation
import Metadata
import ParseState
import Pass
import Types

--{{{ setup stuff for Parsec
type OccParser = GenParser Char ParseState

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
                          "#INCLUDE",
                          "#USE",
                          indentMarker,
                          outdentMarker,
                          eolMarker,
                          mainMarker
                         ]
    , P.caseSensitive  = True
    }

lexer :: P.TokenParser ParseState
lexer  = P.makeTokenParser occamStyle

-- XXX replace whitespace with something that doesn't eat \ns

whiteSpace = P.whiteSpace lexer
lexeme = P.lexeme lexer
symbol = P.symbol lexer
natural = P.natural lexer
parens = P.parens lexer
semi = P.semi lexer
identifier = P.identifier lexer
reserved = P.reserved lexer
reservedOp = P.reservedOp lexer
--}}}

--{{{ symbols
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
sApos = try $ symbol "'"
sQuote = try $ symbol "\""
sHash = try $ symbol "#"
--}}}
--{{{ keywords
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
sppINCLUDE = reserved "#INCLUDE"
sppUSE = reserved "#USE"
--}}}
--{{{ markers inserted by the preprocessor
-- XXX could handle VALOF by translating each step to one { and matching multiple ones?
mainMarker = "__main"

sMainMarker = do { whiteSpace; reserved mainMarker } <?> "end of input (top-level process)"

indent = do { whiteSpace; reserved indentMarker } <?> "indentation increase"
outdent = do { whiteSpace; reserved outdentMarker } <?> "indentation decrease"
eol = do { whiteSpace; reserved eolMarker } <?> "end of line"
--}}}

--{{{ helper functions
getSourcePos :: OccParser OccSourcePos
getSourcePos
  =  do pos <- getPosition
        return $ OccSourcePos (sourceName pos) (sourceLine pos) (sourceColumn pos)

md :: OccParser Meta
md
  =  do pos <- getSourcePos
        return [MdSourcePos pos]

tryVX :: OccParser a -> OccParser b -> OccParser a
tryVX p q = try (do { v <- p; q; return v })

tryXV :: OccParser a -> OccParser b -> OccParser b
tryXV p q = try (do { p; q })

tryXVV :: OccParser a -> OccParser b -> OccParser c -> OccParser (b, c)
tryXVV a b c = try (do { a; bv <- b; cv <- c; return (bv, cv) })

tryXVX :: OccParser a -> OccParser b -> OccParser c -> OccParser b
tryXVX a b c = try (do { a; bv <- b; c; return bv })

tryVXV :: OccParser a -> OccParser b -> OccParser c -> OccParser (a, c)
tryVXV a b c = try (do { av <- a; b; cv <- c; return (av, cv) })

maybeSubscripted :: String -> OccParser a -> (Meta -> A.Subscript -> a -> a) -> (a -> OccParser A.Type) -> OccParser a
maybeSubscripted prodName inner subscripter typer
    =  do m <- md
          v <- inner
          t <- typer v
          subs <- postSubscripts t
          return $ foldl (\var sub -> subscripter m sub var) v subs
    <?> prodName

postSubscripts :: A.Type -> OccParser [A.Subscript]
postSubscripts t
    = (do sub <- postSubscript t
          t' <- pSubscriptType sub t
          rest <- postSubscripts t'
          return $ sub : rest)
      <|> return []

postSubscript :: A.Type -> OccParser A.Subscript
postSubscript t
    =  do m <- md
          case t of
            A.UserDataType _ ->
              do f <- tryXV sLeft fieldName
                 sRight
                 return $ A.SubscriptField m f
            A.Array _ _ ->
              do e <- tryXV sLeft intExpr
                 sRight
                 return $ A.Subscript m e
            _ ->
              fail $ "subscript of non-array/record type " ++ show t

maybeSliced :: OccParser a -> (Meta -> A.Subscript -> a -> a) -> (a -> OccParser A.Type) -> OccParser a
maybeSliced inner subscripter typer
    =  do m <- md

          (v, ff1) <- tryXVV sLeft inner fromOrFor
          t <- typer v
          case t of
            (A.Array _ _) -> return ()
            _ -> fail $ "slice of non-array type " ++ show t

          e <- intExpr
          sub <- case ff1 of
                   "FROM" ->
                     (do f <- tryXV sFOR intExpr
                         sRight
                         return $ A.SubscriptFromFor m e f)
                     <|>
                     (do sRight
                         return $ A.SubscriptFrom m e)
                   "FOR" ->
                     do sRight
                        return $ A.SubscriptFor m e

          return $ subscripter m sub v
  where
    fromOrFor :: OccParser String
    fromOrFor = (sFROM >> return "FROM") <|> (sFOR >> return "FOR")

handleSpecs :: OccParser [A.Specification] -> OccParser a -> (Meta -> A.Specification -> a -> a) -> OccParser a
handleSpecs specs inner specMarker
    =   do m <- md
           ss <- specs
           ss' <- mapM scopeInSpec ss
           v <- inner
           mapM scopeOutSpec ss'
           return $ foldl (\e s -> specMarker m s e) v ss'

-- | Like sepBy1, but not eager: it won't consume the separator unless it finds
-- another item after it.
sepBy1NE :: OccParser a -> OccParser b -> OccParser [a]
sepBy1NE item sep
    =  do i <- item
          rest <- option [] $ try (do sep
                                      sepBy1NE item sep)
          return $ i : rest

-- | Run several different parsers with a separator between them.
-- If you give it [a, b, c] and s, it'll parse [a, s, b, s, c] then
-- give you back the results from [a, b, c].
intersperseP :: [OccParser a] -> OccParser b -> OccParser [a]
intersperseP [] _ = return []
intersperseP [f] _
    =  do a <- f
          return [a]
intersperseP (f:fs) sep
    =  do a <- f
          sep
          as <- intersperseP fs sep
          return $ a : as

listType :: Meta -> [A.Type] -> OccParser A.Type
listType m l = listType' m (length l) l
  where
    listType' m len [] = fail "expected non-empty list"
    listType' m len [t] = return $ makeArrayType (A.Dimension $ makeConstant m len) t
    listType' m len (t1 : rest@(t2 : _))
        = if t1 == t2 then listType' m len rest
                      else fail "multiple types in list"

matchType :: A.Type -> A.Type -> OccParser ()
matchType et rt
    = case (et, rt) of
        ((A.Array ds t), (A.Array ds' t')) ->
          if length ds == length ds' then return () else bad
        _ -> if rt == et then return () else bad
  where
    bad = fail $ "type mismatch (got " ++ show rt ++ "; expected " ++ show et ++ ")"

checkMaybe :: String -> Maybe a -> OccParser a
checkMaybe msg op
    = case op of
        Just t -> return t
        Nothing -> fail msg

pTypeOf :: (ParseState -> a -> Maybe b) -> a -> OccParser b
pTypeOf f item
    =  do st <- getState
          checkMaybe "cannot compute type" $ f st item

pTypeOfVariable = pTypeOf typeOfVariable
pTypeOfLiteral = pTypeOf typeOfLiteral
pTypeOfExpression = pTypeOf typeOfExpression
pSpecTypeOfName = pTypeOf specTypeOfName

pSubscriptType :: A.Subscript -> A.Type -> OccParser A.Type
pSubscriptType sub t
    =  do st <- getState
          checkMaybe "cannot subscript type" $ subscriptType st sub t
--}}}

--{{{ name scoping
findName :: A.Name -> OccParser A.Name
findName thisN
    =  do st <- getState
          origN <- case lookup (A.nameName thisN) (psLocalNames st) of
                     Nothing -> fail $ "name " ++ A.nameName thisN ++ " not defined"
                     Just n -> return n
          if A.nameType thisN /= A.nameType origN
            then fail $ "expected " ++ show (A.nameType thisN) ++ " (" ++ A.nameName origN ++ " is " ++ show (A.nameType origN) ++ ")"
            else return $ thisN { A.nameName = A.nameName origN }

scopeIn :: A.Name -> A.SpecType -> A.AbbrevMode -> OccParser A.Name
scopeIn n@(A.Name m nt s) t am
    =  do st <- getState
          let s' = s ++ "_u" ++ (show $ psNameCounter st)
          let n' = n { A.nameName = s' }
          let nd = A.NameDef {
            A.ndMeta = m,
            A.ndName = s',
            A.ndOrigName = s,
            A.ndNameType = A.nameType n',
            A.ndType = t,
            A.ndAbbrevMode = am
          }
          setState $ psDefineName n' nd $ st {
            psNameCounter = (psNameCounter st) + 1,
            psLocalNames = (s, n') : (psLocalNames st)
            }
          return n'

scopeOut :: A.Name -> OccParser ()
scopeOut n@(A.Name m nt s)
    =  do st <- getState
          let lns' = case psLocalNames st of
                       (s, _):ns -> ns
                       otherwise -> dieInternal "scopeOut trying to scope out the wrong name"
          setState $ st { psLocalNames = lns' }

-- FIXME: Do these with generics? (going carefully to avoid nested code blocks)
scopeInRep :: A.Replicator -> OccParser A.Replicator
scopeInRep (A.For m n b c)
    =  do n' <- scopeIn n (A.Declaration m A.Int) A.ValAbbrev
          return $ A.For m n' b c

scopeOutRep :: A.Replicator -> OccParser ()
scopeOutRep (A.For m n b c) = scopeOut n

-- This one's more complicated because we need to check if we're introducing a constant.
scopeInSpec :: A.Specification -> OccParser A.Specification
scopeInSpec (A.Specification m n st)
    =  do ps <- getState
          let (st', isConst) = case st of
                                 (A.IsExpr m A.ValAbbrev t e) ->
                                   case simplifyExpression ps e of
                                     Left _ -> (st, False)
                                     Right e' -> (A.IsExpr m A.ValAbbrev t e', True)
                                 _ -> (st, False)
          n' <- scopeIn n st' (abbrevModeOfSpec st')
          if isConst
            then updateState (\ps -> ps { psConstants = (A.nameName n', case st' of A.IsExpr _ _ _ e' -> e') : psConstants ps })
            else return ()
          return $ A.Specification m n' st'

scopeOutSpec :: A.Specification -> OccParser ()
scopeOutSpec (A.Specification _ n _) = scopeOut n

scopeInFormal :: A.Formal -> OccParser A.Formal
scopeInFormal (A.Formal am t n)
    =  do n' <- scopeIn n (A.Declaration (A.nameMeta n) t) am
          return (A.Formal am t n')

scopeInFormals :: [A.Formal] -> OccParser [A.Formal]
scopeInFormals fs = mapM scopeInFormal fs

scopeOutFormals :: [A.Formal] -> OccParser ()
scopeOutFormals fs = sequence_ [scopeOut n | (A.Formal am t n) <- fs]

--}}}

--{{{ grammar productions
-- These productions are (now rather loosely) based on the ordered syntax in
-- the occam2.1 manual.
--
-- Each production is allowed to consume the thing it's trying to match.

--{{{ names
anyName :: A.NameType -> OccParser A.Name
anyName nt
    =   do m <- md
           s <- identifier
           return $ A.Name m nt s
    <?> show nt

name :: A.NameType -> OccParser A.Name
name nt
    =   do n <- anyName nt
           findName n

newName :: A.NameType -> OccParser A.Name
newName nt = anyName nt

channelName = name A.ChannelName
dataTypeName = name A.DataTypeName
functionName = name A.FunctionName
portName = name A.PortName
procName = name A.ProcName
protocolName = name A.ProtocolName
timerName = name A.TimerName
variableName = name A.VariableName

newChannelName = newName A.ChannelName
newDataTypeName = newName A.DataTypeName
newFunctionName = newName A.FunctionName
newPortName = newName A.PortName
newProcName = newName A.ProcName
newProtocolName = newName A.ProtocolName
newTimerName = newName A.TimerName
newVariableName = newName A.VariableName

-- These are special because their scope is only valid within the particular
-- record or protocol they're used in.
fieldName = anyName A.FieldName
tagName = anyName A.TagName
newFieldName = anyName A.FieldName
newTagName = anyName A.TagName
--}}}
--{{{ types
dataType :: OccParser A.Type
dataType
    =   do { sBOOL; return A.Bool }
    <|> do { sBYTE; return A.Byte }
    <|> do { sINT; return A.Int }
    <|> do { sINT16; return A.Int16 }
    <|> do { sINT32; return A.Int32 }
    <|> do { sINT64; return A.Int64 }
    <|> do { sREAL32; return A.Real32 }
    <|> do { sREAL64; return A.Real64 }
    <|> try (do { sLeft; s <- constIntExpr; sRight; t <- dataType; return $ makeArrayType (A.Dimension s) t })
    <|> do { n <- dataTypeName; return $ A.UserDataType n }
    <?> "dataType"

-- FIXME should probably make CHAN INT work, since that'd be trivial...
channelType :: OccParser A.Type
channelType
    =   do { sCHAN; sOF; p <- protocol; return $ A.Chan p }
    <|> try (do { sLeft; s <- constIntExpr; sRight; t <- channelType; return $ makeArrayType (A.Dimension s) t })
    <?> "channelType"

timerType :: OccParser A.Type
timerType
    =   do { sTIMER; return $ A.Timer }
    <|> try (do { sLeft; s <- constIntExpr; sRight; t <- timerType; return $ makeArrayType (A.Dimension s) t })
    <?> "timerType"

portType :: OccParser A.Type
portType
    =   do { sPORT; sOF; p <- dataType; return $ A.Port p }
    <|> do { m <- md; try sLeft; s <- try constIntExpr; try sRight; t <- portType; return $ makeArrayType (A.Dimension s) t }
    <?> "portType"
--}}}
--{{{ literals
literal :: OccParser A.Literal
literal
    =   try (do { m <- md; v <- real; sLeftR; t <- dataType; sRightR; return $ A.Literal m t v })
    <|> try (do { m <- md; v <- integer; sLeftR; t <- dataType; sRightR; return $ A.Literal m t v })
    <|> try (do { m <- md; v <- byte; sLeftR; t <- dataType; sRightR; return $ A.Literal m t v })
    <|> try (do { m <- md; r <- real; return $ A.Literal m A.Real32 r })
    <|> try (do { m <- md; r <- integer; return $ A.Literal m A.Int r })
    <|> try (do { m <- md; r <- byte; return $ A.Literal m A.Byte r })
    <?> "literal"

real :: OccParser A.LiteralRepr
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

occamExponent :: OccParser String
occamExponent
    =   try (do { c <- oneOf "+-"; d <- digits; return $ c : d })
    <?> "exponent"

integer :: OccParser A.LiteralRepr
integer
    =   try (do { m <- md; d <- lexeme digits; return $ A.IntLiteral m d })
    <|> do { m <- md; sHash; d <- many1 hexDigit; return $ A.HexLiteral m d }
    <?> "integer"

digits :: OccParser String
digits
    =   many1 digit
    <?> "digits"

byte :: OccParser A.LiteralRepr
byte
    =   do { m <- md; char '\''; s <- character; sApos; return $ A.ByteLiteral m s }
    <?> "byte"

-- i.e. array literal
table :: OccParser A.Literal
table
    = maybeSubscripted "table" table' A.SubscriptedLiteral pTypeOfLiteral

table' :: OccParser A.Literal
table'
    -- FIXME Check dimensions match
    =   try (do { m <- md; (s, dim) <- stringLiteral; sLeftR; t <- dataType; sRightR; return $ A.Literal m t s })
    <|> try (do { m <- md; (s, dim) <- stringLiteral; return $ A.Literal m (A.Array [dim] A.Byte) s })
    <|> do m <- md
           es <- tryXVX sLeft (sepBy1 expression sComma) sRight
           ps <- getState
           ets <- mapM (\e -> checkMaybe "can't type expression" $ typeOfExpression ps e) es
           t <- listType m ets
           return $ A.Literal m t (A.ArrayLiteral m es)
    <|> maybeSliced table A.SubscriptedLiteral pTypeOfLiteral
    <?> "table'"

stringLiteral :: OccParser (A.LiteralRepr, A.Dimension)
stringLiteral
    =   do { m <- md; char '"'; cs <- manyTill character sQuote; return $ (A.StringLiteral m $ concat cs, A.Dimension $ makeConstant m $ length cs) }
    <?> "stringLiteral"

character :: OccParser String
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
--}}}
--{{{ expressions
functionNameSingle :: OccParser A.Name
    =  do n <- functionName
          rts <- (pTypeOf returnTypesOfFunction) n
          case rts of
            [_] -> return n
            _ -> pzero
    <?> "function with single return value"

functionNameMulti :: OccParser A.Name
    =  do n <- functionName
          rts <- (pTypeOf returnTypesOfFunction) n
          case rts of
            [_] -> pzero
            _ -> return n
    <?> "function with multiple return values"

expressionList :: OccParser A.ExpressionList
expressionList
    =   try (do { m <- md; n <- functionNameMulti; sLeftR; as <- sepBy expression sComma; sRightR; return $ A.FunctionCallList m n as })
    <|> do { m <- md; es <- sepBy1 expression sComma; return $ A.ExpressionList m es }
-- XXX: Value processes are not supported (because nobody uses them and they're hard to parse)
    <?> "expressionList"

expression :: OccParser A.Expression
expression
    =   do { m <- md; o <- monadicOperator; v <- operand; return $ A.Monadic m o v }
    <|> do { m <- md; sMOSTPOS; t <- dataType; return $ A.MostPos m t }
    <|> do { m <- md; sMOSTNEG; t <- dataType; return $ A.MostNeg m t }
    <|> sizeExpr
    <|> do { m <- md; sTRUE; return $ A.True m }
    <|> do { m <- md; sFALSE; return $ A.False m }
    <|> try (do { m <- md; l <- operand; o <- dyadicOperator; r <- operand; return $ A.Dyadic m o l r })
    <|> try conversion
    <|> operand
    <?> "expression"

sizeExpr :: OccParser A.Expression
sizeExpr
    =  do m <- md
          sSIZE
          (try (do { t <- dataType; return $ A.SizeType m t })
           <|> do { v <- operand; return $ A.SizeExpr m v }
           <|> do { v <- channel <|> timer <|> port; return $ A.SizeVariable m v })
    <?> "sizeExpr"

exprOfType :: A.Type -> OccParser A.Expression
exprOfType wantT
    =  do e <- expression
          t <- pTypeOfExpression e
          matchType wantT t
          return e

intExpr = exprOfType A.Int <?> "integer expression"
booleanExpr = exprOfType A.Bool <?> "boolean expression"

constExprOfType :: A.Type -> OccParser A.Expression
constExprOfType wantT
    =  do e <- exprOfType wantT
          ps <- getState
          case simplifyExpression ps e of
            Left err -> fail $ "expected constant expression (" ++ err ++ ")"
            Right e' -> return e'

constIntExpr = constExprOfType A.Int <?> "constant integer expression"

monadicOperator :: OccParser A.MonadicOp
monadicOperator
    =   do { reservedOp "-" <|> sMINUS; return A.MonadicSubtr }
    <|> do { reservedOp "~" <|> sBITNOT; return A.MonadicBitNot }
    <|> do { sNOT; return A.MonadicNot }
    <?> "monadicOperator"

dyadicOperator :: OccParser A.DyadicOp
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

conversion :: OccParser A.Expression
conversion
    =   try (do m <- md
                t <- dataType
                (c, o) <- conversionMode
                return $ A.Conversion m c t o)
    <?> "conversion"

conversionMode :: OccParser (A.ConversionMode, A.Expression)
conversionMode
    =   do { sROUND; o <- operand; return (A.Round, o) }
    <|> do { sTRUNC; o <- operand; return (A.Trunc, o) }
    -- This uses operandNotTable to resolve the "x[y]" ambiguity.
    <|> do { o <- operandNotTable; return (A.DefaultConversion, o) }
    <?> "conversionMode"
--}}}
--{{{ operands
operand :: OccParser A.Expression
operand
    = maybeSubscripted "operand" operand' A.SubscriptedExpr pTypeOfExpression

operand' :: OccParser A.Expression
operand'
    =   try (do { m <- md; l <- table; return $ A.ExprLiteral m l })
    <|> operandNotTable'
    <?> "operand'"

operandNotTable :: OccParser A.Expression
operandNotTable
    = maybeSubscripted "operandNotTable" operandNotTable' A.SubscriptedExpr pTypeOfExpression

operandNotTable' :: OccParser A.Expression
operandNotTable'
    =   try (do { m <- md; v <- variable; return $ A.ExprVariable m v })
    <|> try (do { m <- md; l <- literal; return $ A.ExprLiteral m l })
    <|> try (do { sLeftR; e <- expression; sRightR; return e })
-- XXX value process
    <|> try (do { m <- md; n <- functionNameSingle; sLeftR; as <- sepBy expression sComma; sRightR; return $ A.FunctionCall m n as })
    <|> try (do { m <- md; sBYTESIN; sLeftR; o <- operand; sRightR; return $ A.BytesInExpr m o })
    <|> try (do { m <- md; sBYTESIN; sLeftR; t <- dataType; sRightR; return $ A.BytesInType m t })
    <|> try (do { m <- md; sOFFSETOF; sLeftR; t <- dataType; sComma; f <- fieldName; sRightR; return $ A.OffsetOf m t f })
    <?> "operandNotTable'"
--}}}
--{{{ variables, channels, timers, ports
variable :: OccParser A.Variable
variable
    = maybeSubscripted "variable" variable' A.SubscriptedVariable pTypeOfVariable

variable' :: OccParser A.Variable
variable'
    =   try (do { m <- md; n <- variableName; return $ A.Variable m n })
    <|> try (maybeSliced variable A.SubscriptedVariable pTypeOfVariable)
    <?> "variable'"

channel :: OccParser A.Variable
channel
    =   maybeSubscripted "channel" channel' A.SubscriptedVariable pTypeOfVariable
    <?> "channel"

channel' :: OccParser A.Variable
channel'
    =   try (do { m <- md; n <- channelName; return $ A.Variable m n })
    <|> try (maybeSliced channel A.SubscriptedVariable pTypeOfVariable)
    <?> "channel'"

timer :: OccParser A.Variable
timer
    =   maybeSubscripted "timer" timer' A.SubscriptedVariable pTypeOfVariable
    <?> "timer"

timer' :: OccParser A.Variable
timer'
    =   try (do { m <- md; n <- timerName; return $ A.Variable m n })
    <|> try (maybeSliced timer A.SubscriptedVariable pTypeOfVariable)
    <?> "timer'"

port :: OccParser A.Variable
port
    =   maybeSubscripted "port" port' A.SubscriptedVariable pTypeOfVariable
    <?> "port"

port' :: OccParser A.Variable
port'
    =   try (do { m <- md; n <- portName; return $ A.Variable m n })
    <|> try (maybeSliced port A.SubscriptedVariable pTypeOfVariable)
    <?> "port'"
--}}}
--{{{ protocols
protocol :: OccParser A.Type
protocol
    =   try (do { n <- protocolName ; return $ A.UserProtocol n })
    <|> simpleProtocol
    <?> "protocol"

simpleProtocol :: OccParser A.Type
simpleProtocol
    =   try (do { l <- dataType; sColons; sLeft; sRight; r <- dataType; return $ A.Counted l r })
    <|> dataType
    <|> do { sANY; return $ A.Any }
    <?> "simpleProtocol"

sequentialProtocol :: OccParser [A.Type]
sequentialProtocol
    =   do { l <- try $ sepBy1 simpleProtocol sSemi; return l }
    <?> "sequentialProtocol"

taggedProtocol :: OccParser (A.Name, [A.Type])
taggedProtocol
    =   try (do { t <- newTagName; eol; return (t, [])  })
    <|> try (do { t <- newTagName; sSemi; sp <- sequentialProtocol; eol; return (t, sp) })
    <?> "taggedProtocol"
--}}}
--{{{ replicators
replicator :: OccParser A.Replicator
replicator
    =  do m <- md
          n <- tryVX newVariableName sEq
          b <- intExpr
          sFOR
          c <- intExpr
          return $ A.For m n b c
    <?> "replicator"
--}}}
--{{{ specifications, declarations, allocations
allocation :: OccParser [A.Specification]
allocation
    =   do { m <- md; sPLACE; n <- variableName; sAT; e <- intExpr; sColon; eol; return [A.Specification m n (A.Place m e)] }
    <?> "allocation"

specification :: OccParser [A.Specification]
specification
    =   try (do { m <- md; (ns, d) <- declaration; return [A.Specification m n d | n <- ns] })
    <|> try (do { a <- abbreviation; return [a] })
    <|> do { d <- definition; return [d] }
    <?> "specification"

declaration :: OccParser ([A.Name], A.SpecType)
declaration
    =   do { m <- md; d <- dataType; ns <- sepBy1 newVariableName sComma; sColon; eol; return (ns, A.Declaration m d) }
    <|> do { m <- md; d <- channelType; ns <- sepBy1 newChannelName sComma; sColon; eol; return (ns, A.Declaration m d) }
    <|> do { m <- md; d <- timerType; ns <- sepBy1 newTimerName sComma; sColon; eol; return (ns, A.Declaration m d) }
    <|> do { m <- md; d <- portType; ns <- sepBy1 newPortName sComma; sColon; eol; return (ns, A.Declaration m d) }
    <?> "declaration"

abbreviation :: OccParser A.Specification
abbreviation
    =   do m <- md
           (do { (n, v) <- tryVXV newVariableName sIS variable; sColon; eol; t <- pTypeOfVariable v; return $ A.Specification m n $ A.Is m A.Abbrev t v }
            <|> do { (s, n, v) <- try (do { s <- specifier; n <- newVariableName; sIS; v <- variable; return (s, n, v) }); sColon; eol; t <- pTypeOfVariable v; matchType s t; return $ A.Specification m n $ A.Is m A.Abbrev s v }
            <|> valIsAbbrev
            <|> try (do { n <- newChannelName; sIS; c <- channel; sColon; eol; t <- pTypeOfVariable c; return $ A.Specification m n $ A.Is m A.Abbrev t c })
            <|> try (do { n <- newTimerName; sIS; c <- timer; sColon; eol; t <- pTypeOfVariable c; return $ A.Specification m n $ A.Is m A.Abbrev t c })
            <|> try (do { n <- newPortName; sIS; c <- port; sColon; eol; t <- pTypeOfVariable c; return $ A.Specification m n $ A.Is m A.Abbrev t c })
            <|> try (do { s <- specifier; n <- newChannelName; sIS; c <- channel; sColon; eol; t <- pTypeOfVariable c; matchType s t; return $ A.Specification m n $ A.Is m A.Abbrev s c })
            <|> try (do { s <- specifier; n <- newTimerName; sIS; c <- timer; sColon; eol; t <- pTypeOfVariable c; matchType s t; return $ A.Specification m n $ A.Is m A.Abbrev s c })
            <|> try (do { s <- specifier; n <- newPortName; sIS; c <- port; sColon; eol; t <- pTypeOfVariable c; matchType s t; return $ A.Specification m n $ A.Is m A.Abbrev s c })
            <|> try (do { n <- newChannelName; sIS; sLeft; cs <- sepBy1 channel sComma; sRight; sColon; eol; ts <- mapM pTypeOfVariable cs; t <- listType m ts; return $ A.Specification m n $ A.IsChannelArray m t cs })
            <|> try (do { s <- specifier; n <- newChannelName; sIS; sLeft; cs <- sepBy1 channel sComma; sRight; sColon; eol; ts <- mapM pTypeOfVariable cs; t <- listType m ts; matchType s t; return $ A.Specification m n $ A.IsChannelArray m s cs }))
    <?> "abbreviation"

valIsAbbrev :: OccParser A.Specification
valIsAbbrev
    =  do m <- md
          sVAL
          (n, t, e) <- do { (n, e) <- tryVXV newVariableName sIS expression; sColon; eol; t <- pTypeOfExpression e; return (n, t, e) }
                       <|> do { s <- specifier; n <- newVariableName; sIS; e <- expression; sColon; eol; t <- pTypeOfExpression e; matchType s t; return (n, t, e) }
          return $ A.Specification m n $ A.IsExpr m A.ValAbbrev t e
    <?> "VAL IS abbreviation"

definition :: OccParser A.Specification
definition
    =   do {  m <- md; sDATA; sTYPE; n <- newDataTypeName ;
              do {sIS; t <- dataType; sColon; eol; return $ A.Specification m n (A.DataType m t) }
              <|> do { eol; indent; rec <- structuredType; outdent; sColon; eol; return $ A.Specification m n rec } }
    <|> do {  m <- md; sPROTOCOL; n <- newProtocolName ;
              do { sIS; p <- sequentialProtocol; sColon; eol; return $ A.Specification m n $ A.Protocol m p }
              <|> do { eol; indent; sCASE; eol; indent; ps <- many1 taggedProtocol; outdent; outdent; sColon; eol; return $ A.Specification m n $ A.ProtocolCase m ps } }
    <|> do { m <- md; sPROC; n <- newProcName; fs <- formalList; eol; indent; fs' <- scopeInFormals fs; p <- process; scopeOutFormals fs'; outdent; sColon; eol; return $ A.Specification m n $ A.Proc m fs' p }
    <|> try (do { m <- md; rs <- sepBy1 dataType sComma; (n, fs) <- functionHeader ;
                  do { sIS; fs' <- scopeInFormals fs; el <- expressionList; scopeOutFormals fs'; sColon; eol; return $ A.Specification m n $ A.Function m rs fs' (A.ValOf m (A.Skip m) el) }
                  <|> do { eol; indent; fs' <- scopeInFormals fs; vp <- valueProcess; scopeOutFormals fs'; outdent; sColon; eol; return $ A.Specification m n $ A.Function m rs fs' vp } })
    <|> try (do { m <- md; s <- specifier; n <- newVariableName ;
                  sRETYPES <|> sRESHAPES; v <- variable; sColon; eol; return $ A.Specification m n $ A.Retypes m A.Abbrev s v })
    <|> try (do {  m <- md; sVAL; s <- specifier; n <- newVariableName ;
                   sRETYPES <|> sRESHAPES; e <- expression; sColon; eol; return $ A.Specification m n $ A.RetypesExpr m A.ValAbbrev s e })
    <?> "definition"

dataSpecifier :: OccParser A.Type
dataSpecifier
    =   try dataType
    <|> try (do { sLeft; sRight; s <- dataSpecifier; return $ makeArrayType A.UnknownDimension s })
    <?> "dataSpecifier"

specifier :: OccParser A.Type
specifier
    =   try dataType
    <|> try channelType
    <|> try timerType
    <|> try portType
    <|> try (do { sLeft; sRight; s <- specifier; return $ makeArrayType A.UnknownDimension s })
    <?> "specifier"

--{{{ PROCs and FUNCTIONs
formalList :: OccParser [A.Formal]
formalList
    =  do m <- md
          sLeftR
          fs <- sepBy formalArgSet sComma
          sRightR
          return $ concat fs
    <?> "formalList"

formalArgSet :: OccParser [A.Formal]
formalArgSet
    =   try (do (am, t) <- formalVariableType
                ns <- sepBy1NE newVariableName sComma
                return [A.Formal am t n | n <- ns])
    <|> do t <- specifier
           ns <- sepBy1NE newChannelName sComma
           return [A.Formal A.Abbrev t n | n <- ns]
    <?> "formalArgSet"

formalVariableType :: OccParser (A.AbbrevMode, A.Type)
    =   try (do { sVAL; s <- dataSpecifier; return (A.ValAbbrev, s) })
    <|> do { s <- dataSpecifier; return (A.Abbrev, s) }
    <?> "formalVariableType"

functionHeader :: OccParser (A.Name, [A.Formal])
functionHeader
    =   do { sFUNCTION; n <- newFunctionName; fs <- formalList; return $ (n, fs) }
    <?> "functionHeader"

valueProcess :: OccParser A.ValueProcess
valueProcess
    =   try (do { m <- md; sVALOF; eol; indent; p <- process; sRESULT; el <- expressionList; eol; outdent; return $ A.ValOf m p el })
    <|> handleSpecs specification valueProcess A.ValOfSpec
--}}}
--{{{ RECORDs
structuredType :: OccParser A.SpecType
structuredType
    =   do m <- md
           isPacked <- recordKeyword
           eol
           indent
           fs <- many1 structuredTypeField
           outdent
           return $ A.DataTypeRecord m isPacked (concat fs)
    <?> "structuredType"

recordKeyword :: OccParser Bool
recordKeyword
    =   do { sPACKED; sRECORD; return True }
    <|> do { sRECORD; return False }
    <?> "recordKeyword"

structuredTypeField :: OccParser [(A.Name, A.Type)]
structuredTypeField
    =   do { t <- dataType; fs <- many1 newFieldName; sColon; eol; return [(f, t) | f <- fs]  }
    <?> "structuredTypeField"
--}}}
--}}}
--{{{ processes
process :: OccParser A.Process
process
    =   assignment
    <|> caseInput
    <|> inputProcess
    <|> output
    <|> do { m <- md; sSKIP; eol; return $ A.Skip m }
    <|> do { m <- md; sSTOP; eol; return $ A.Stop m }
    <|> seqProcess
    <|> ifProcess
    <|> caseProcess
    <|> whileProcess
    <|> parallel
    <|> altProcess
    <|> procInstance
    <|> mainProcess
    <|> handleSpecs (allocation <|> specification) process A.ProcSpec
    <|> preprocessorDirective
    <?> "process"

--{{{ assignment (:=)
assignment :: OccParser A.Process
assignment
    =   do { m <- md; vs <- tryVX variableList sAssign; es <- expressionList; eol; return $ A.Assign m vs es }
    <?> "assignment"

variableList :: OccParser [A.Variable]
variableList
    =   do { vs <- sepBy1 variable sComma; return $ vs }
    <?> "variableList"
--}}}
--{{{ input (?)
inputProcess :: OccParser A.Process
inputProcess
    =   do m <- md
           (c, i) <- input
           return $ A.Input m c i

input :: OccParser (A.Variable, A.InputMode)
input
    =   channelInput
    <|> timerInput
    <|> do { m <- md; p <- tryVX port sQuest; v <- variable; eol; return (p, A.InputSimple m [A.InVariable m v]) }
    <?> "input"

channelInput :: OccParser (A.Variable, A.InputMode)
    =   do  m <- md
            c <- tryVX channel sQuest
            (do { tl <- try (do { sCASE; taggedList }); eol; return (c, A.InputCase m (A.OnlyV m (tl (A.Skip m)))) }
             <|> do { sAFTER; e <- intExpr; eol; return (c, A.InputAfter m e) }
             <|> do { is <- sepBy1 inputItem sSemi; eol; return (c, A.InputSimple m is) })
    <?> "channelInput"

timerInput :: OccParser (A.Variable, A.InputMode)
    =   do  m <- md
            c <- tryVX timer sQuest
            (do { v <- variable; eol; return (c, A.InputSimple m [A.InVariable m v]) }
             <|> do { sAFTER; e <- intExpr; eol; return (c, A.InputAfter m e) })
    <?> "timerInput"

taggedList :: OccParser (A.Process -> A.Variant)
taggedList
    =   try (do { m <- md; t <- tagName; sSemi; is <- sepBy1 inputItem sSemi; return $ A.Variant m t is })
    <|> do { m <- md; t <- tagName; return $ A.Variant m t [] }
    <?> "taggedList"

inputItem :: OccParser A.InputItem
inputItem
    =   try (do { m <- md; v <- variable; sColons; w <- variable; return $ A.InCounted m v w })
    <|> do { m <- md; v <- variable; return $ A.InVariable m v }
    <?> "inputItem"
--}}}
--{{{ variant input (? CASE)
caseInput :: OccParser A.Process
caseInput
    =  do m <- md
          c <- tryVX channel (do {sQuest; sCASE; eol})
          indent
          vs <- many1 variant
          outdent
          return $ A.Input m c (A.InputCase m (A.Several m vs))
    <?> "caseInput"

variant :: OccParser A.Structured
variant
    =   try (do { m <- md; tl <- taggedList; eol; indent; p <- process; outdent; return $ A.OnlyV m (tl p) })
    <|> handleSpecs specification variant A.Spec
    <?> "variant"
--}}}
--{{{ output (!)
output :: OccParser A.Process
output
    =   channelOutput
    <|> do { m <- md; p <- tryVX port sBang; e <- expression; eol; return $ A.Output m p [A.OutExpression m e] }
    <?> "output"

channelOutput :: OccParser A.Process
channelOutput
    =   do  m <- md
            c <- tryVX channel sBang
            -- This is an ambiguity in the occam grammar; you can't tell in "a ! b"
            -- whether b is a variable or a tag, without knowing the type of a.
            st <- getState
            isCase <- case typeOfVariable st c of
                        Just t -> return $ isCaseProtocolType st t
                        Nothing -> fail $ "cannot figure out the type of " ++ show c
            if isCase
              then
                (try (do { t <- tagName; sSemi; os <- sepBy1 outputItem sSemi; eol; return $ A.OutputCase m c t os })
                 <|> do { t <- tagName; eol; return $ A.OutputCase m c t [] })
              else
                do { os <- sepBy1 outputItem sSemi; eol; return $ A.Output m c os }
    <?> "channelOutput"

outputItem :: OccParser A.OutputItem
outputItem
    =   try (do { m <- md; a <- intExpr; sColons; b <- expression; return $ A.OutCounted m a b })
    <|> do { m <- md; e <- expression; return $ A.OutExpression m e }
    <?> "outputItem"
--}}}
--{{{ SEQ
seqProcess :: OccParser A.Process
seqProcess
    =   do  m <- md
            sSEQ
            (do { eol; indent; ps <- many1 process; outdent; return $ A.Seq m ps }
             <|> do { r <- replicator; eol; indent; r' <- scopeInRep r; p <- process; scopeOutRep r'; outdent; return $ A.SeqRep m r' p })
    <?> "seqProcess"
--}}}
--{{{ IF
ifProcess :: OccParser A.Process
ifProcess
    =   do m <- md
           c <- conditional
           return $ A.If m c
    <?> "ifProcess"

conditional :: OccParser A.Structured
conditional
    =   do {  m <- md; sIF ;
              do { eol; indent; cs <- many1 ifChoice; outdent; return $ A.Several m cs }
              <|> do { r <- replicator; eol; indent; r' <- scopeInRep r; c <- ifChoice; scopeOutRep r'; outdent; return $ A.Rep m r' c } }
    <?> "conditional"

ifChoice :: OccParser A.Structured
ifChoice
    =   guardedChoice
    <|> conditional
    <|> handleSpecs specification ifChoice A.Spec
    <?> "choice"

guardedChoice :: OccParser A.Structured
guardedChoice
    =   do m <- md
           b <- booleanExpr
           eol
           indent
           p <- process
           outdent
           return $ A.OnlyC m (A.Choice m b p)
    <?> "guardedChoice"
--}}}
--{{{ CASE
caseProcess :: OccParser A.Process
caseProcess
    =   do m <- md
           sCASE
           s <- caseSelector
           eol
           indent
           os <- many1 caseOption
           outdent
           return $ A.Case m s (A.Several m os)
    <?> "caseProcess"

caseSelector :: OccParser A.Expression
caseSelector
-- FIXME Should constrain to things that can be CASEd over.
    =   expression
    <?> "caseSelector"

caseOption :: OccParser A.Structured
caseOption
    =   try (do { m <- md; ces <- sepBy caseExpression sComma; eol; indent; p <- process; outdent; return $ A.OnlyO m (A.Option m ces p) })
    <|> try (do { m <- md; sELSE; eol; indent; p <- process; outdent; return $ A.OnlyO m (A.Else m p) })
    <|> handleSpecs specification caseOption A.Spec
    <?> "option"

caseExpression :: OccParser A.Expression
caseExpression
    -- FIXME: Check the type is something constant that CASE can deal with
    =   expression
    <?> "caseExpression"
--}}}
--{{{ WHILE
whileProcess :: OccParser A.Process
whileProcess
    =   do m <- md
           sWHILE
           b <- booleanExpr
           eol
           indent
           p <- process
           outdent
           return $ A.While m b p
    <?> "whileProcess"
--}}}
--{{{ PAR
parallel :: OccParser A.Process
parallel
    =   do m <- md
           isPri <- parKeyword
           (do { eol; indent; ps <- many1 process; outdent; return $ A.Par m isPri ps }
            <|> do { r <- replicator; eol; indent; r' <- scopeInRep r; p <- process; scopeOutRep r'; outdent; return $ A.ParRep m isPri r' p })
    <|> placedpar
    <?> "parallel"

parKeyword :: OccParser A.ParMode
parKeyword
    =   do { sPAR; return A.PlainPar }
    <|> try (do { sPRI; sPAR; return A.PriPar })
    <?> "parKeyword"

-- XXX PROCESSOR as a process isn't really legal, surely?
placedpar :: OccParser A.Process
placedpar
    =   do m <- md
           sPLACED
           sPAR
           (do { eol; indent; ps <- many1 placedpar; outdent; return $ A.Par m A.PlacedPar ps  }
            <|> do { r <- replicator; eol; indent; r' <- scopeInRep r; p <- placedpar; scopeOutRep r'; outdent; return $ A.ParRep m A.PlacedPar r' p })
    <|> do { m <- md; sPROCESSOR; e <- intExpr; eol; indent; p <- process; outdent; return $ A.Processor m e p }
    <?> "placedpar"
--}}}
--{{{ ALT
altProcess :: OccParser A.Process
altProcess
    =   do m <- md
           (isPri, a) <- alternation
           return $ A.Alt m isPri a
    <?> "altProcess"

alternation :: OccParser (Bool, A.Structured)
alternation
    =   do {  m <- md; isPri <- altKeyword ;
              do { eol; indent; as <- many1 alternative; outdent; return (isPri, A.Several m as) }
              <|> do { r <- replicator; eol; indent; r' <- scopeInRep r; a <- alternative; scopeOutRep r'; outdent; return (isPri, A.Rep m r' a) } }
    <?> "alternation"

altKeyword :: OccParser Bool
altKeyword
    =   do { sALT; return False }
    <|> try (do { sPRI; sALT; return True })
    <?> "altKeyword"

-- The reason the CASE guards end up here is because they have to be handled
-- specially: you can't tell until parsing the guts of the CASE what the processes
-- are.
alternative :: OccParser A.Structured
alternative
    =   guardedAlternative
    -- FIXME: Check we don't have PRI ALT inside ALT.
    <|> do { (isPri, a) <- alternation; return a }
    <|> try (do m <- md
                b <- booleanExpr
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

guardedAlternative :: OccParser A.Structured
guardedAlternative
    =   do m <- md
           makeAlt <- guard
           indent
           p <- process
           outdent
           return $ A.OnlyA m (makeAlt p)
    <?> "guardedAlternative"

guard :: OccParser (A.Process -> A.Alternative)
guard
    =   try (do { m <- md; (c, im) <- input; return $ A.Alternative m c im })
    <|> try (do { m <- md; b <- booleanExpr; sAmp; (c, im) <- input; return $ A.AlternativeCond m b c im })
    <|> try (do { m <- md; b <- booleanExpr; sAmp; sSKIP; eol; return $ A.AlternativeSkip m b })
    <?> "guard"
--}}}
--{{{ PROC calls
procInstance :: OccParser A.Process
procInstance
    =  do m <- md
          n <- tryVX procName sLeftR
          st <- pSpecTypeOfName n
          let fs = case st of A.Proc _ fs _ -> fs
          as <- actuals fs
          sRightR
          eol
          return $ A.ProcCall m n as
    <?> "procInstance"

actuals :: [A.Formal] -> OccParser [A.Actual]
actuals fs = intersperseP (map actual fs) sComma

actual :: A.Formal -> OccParser A.Actual
actual (A.Formal am t n)
    =  do case am of
            A.ValAbbrev -> do { e <- expression; et <- pTypeOfExpression e; matchType t et; return $ A.ActualExpression t e } <?> "actual expression for " ++ an
            _ -> if isChannelType t
                   then do { c <- channel; ct <- pTypeOfVariable c; matchType t ct; return $ A.ActualVariable am t c } <?> "actual channel for " ++ an
                   else do { v <- variable; vt <- pTypeOfVariable v; matchType t vt; return $ A.ActualVariable am t v } <?> "actual variable for " ++ an
    where
      an = A.nameName n
--}}}
--{{{ preprocessor directives
preprocessorDirective :: OccParser A.Process
preprocessorDirective
    =   ppInclude
    <|> ppUse
    <?> "preprocessor directive"

ppInclude :: OccParser A.Process
ppInclude
    =  do sppINCLUDE
          char '"'
          file <- manyTill character sQuote
          eol
          includeFile $ concat file

ppUse :: OccParser A.Process
ppUse
    =  do sppUSE
          char '"'
          mod <- manyTill character sQuote
          eol
          let file = mangleModName $ concat mod

          -- Check whether it's been included already.
          ps <- getState
          if file `elem` psLoadedFiles ps
            then process
            else includeFile file

-- | Invoke the parser recursively to handle an included file.
includeFile :: String -> OccParser A.Process
includeFile file
    =  do ps <- getState
          (f, ps') <- parseFile file ps
          setState ps' { psLocalNames = psMainLocals ps' }
          p <- process
          return $ f p
--}}}
--{{{ main process
mainProcess :: OccParser A.Process
mainProcess
    =  do m <- md
          sMainMarker
          eol
          -- Stash the current locals so that we can either restore them
          -- when we get back to the file we included this one from, or
          -- pull the TLP name from them at the end.
          updateState $ (\ps -> ps { psMainLocals = psLocalNames ps })
          return $ A.Main m
--}}}
--}}}
--{{{ top-level forms
-- This is only really true once we've tacked a process onto the bottom; a
-- source file is really a series of specifications, but the later ones need to
-- have the earlier ones in scope, so we can't parse them separately.
sourceFile :: OccParser (A.Process, ParseState)
sourceFile
    =   do whiteSpace
           p <- process
           s <- getState
           return (p, s)
--}}}
--}}}

--{{{  preprocessor
-- XXX Doesn't handle conditionals.

preprocess :: String -> String
preprocess d = parseIndentation $ lines (d ++ "\n" ++ mainMarker)

readSource :: String -> IO String
readSource file
    =  do f <- IO.openFile file IO.ReadMode
          d <- IO.hGetContents f
          return $ preprocess d

-- | Find (via a nasty regex search) all the files that this source file includes.
preFindIncludes :: String -> [String]
preFindIncludes source
    = concat [case matchRegex incRE l of
                Just [_, fn] -> [fn]
                Nothing -> []
              | l <- lines source]
  where
    incRE = mkRegex "^#(INCLUDE|USE) +\"([^\"]*)\""

-- | If a module name doesn't already have a suffix, add one.
mangleModName :: String -> String
mangleModName mod
    = if ".occ" `isSuffixOf` mod || ".inc" `isSuffixOf` mod
        then mod
        else mod ++ ".occ"

-- | Join a relative path to an existing path (i.e. if you're given foo/bar and
-- baz, return foo/baz).
joinPath :: String -> String -> String
joinPath base new
    = case matchRegex pathRE base of
        Just [dir] -> dir ++ new
        Nothing -> new
  where
    pathRE = mkRegex "^(.*/)[^/]*$"

type LoaderM a = StateT ParseState IO a

-- | Load all the source files necessary for a program.
-- We have to do this now, before entering the parser, because the parser
-- doesn't run in the IO monad. If there were a monad transformer version of
-- Parsec then we could just open files as we need them.
loadSource :: String -> ParseState -> IO ParseState
loadSource file ps = execStateT (load file file) ps
  where
    load :: String -> String -> LoaderM ()
    load file realName
        =  do ps <- get
              case lookup file (psSourceFiles ps) of
                Just _ -> return ()
                Nothing ->
                  do progress $ "Loading source file " ++ realName
                     source <- liftIO $ readSource realName
                     modify $ (\ps -> ps { psSourceFiles = (file, source) : psSourceFiles ps })
                     let deps = map mangleModName $ preFindIncludes source
                     sequence_ [load dep (joinPath file dep) | dep <- deps]
--}}}

--{{{  entry points for the parser itself
-- | Test a parser production (for use from ghci while debugging the parser).
testParse :: Show a => OccParser a -> String -> IO ()
testParse prod text
    = do let r = runParser prod emptyState "" text
         putStrLn $ "Result: " ++ show r

-- | Parse a file, returning a function you can apply to make all its
-- definitions available to a process.
parseFile :: Monad m => String -> ParseState -> m (A.Process -> A.Process, ParseState)
parseFile file ps
    =  do let source = fromJust $ lookup file (psSourceFiles ps)
          let ps' = ps { psLoadedFiles = file : psLoadedFiles ps }
          case runParser sourceFile ps' file source of
            Left err -> die $ "Parse error: " ++ show err
            Right (p, ps'') -> return (replaceMain p, ps'')
  where
    replaceMain :: A.Process -> A.Process -> A.Process
    replaceMain (A.ProcSpec m s p) np = A.ProcSpec m s (replaceMain p np)
    replaceMain (A.Main _) np = np

-- | Parse the top level source file in a program.
parseProgram :: Monad m => String -> ParseState -> m (A.Process, ParseState)
parseProgram file ps
    =  do (f, ps') <- parseFile file ps
          return (f $ A.Main [], ps')
--}}}

