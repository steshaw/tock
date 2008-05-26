{-
Tock: a compiler for parallel languages
Copyright (C) 2007, 2008  University of Kent

This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation, either version 2 of the License, or (at your
option) any later version.

This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License along
with this program.  If not, see <http://www.gnu.org/licenses/>.
-}

-- | Parse occam code into an AST.
module ParseOccam (parseOccamProgram) where

import Control.Monad (liftM)
import Control.Monad.State (MonadState, modify, get, put)
import Data.List
import Data.Maybe
import Text.ParserCombinators.Parsec

import qualified AST as A
import CompState
import Errors
import Intrinsics
import LexOccam
import Metadata
import ParseUtils
import Pass
import ShowCode
import Types
import Utils

--{{{ the parser monad
type OccParser = GenParser Token ([WarningReport], CompState)

instance CSMR (GenParser tok (a,CompState)) where
  getCompState = getState >>* snd

-- We can expose only part of the state to make it look like we are only using
-- CompState:
instance MonadState CompState (GenParser tok (a,CompState)) where
  get = getState >>* snd
  put st = do (other, _) <- getState
              setState (other, st)

-- The other part of the state is actually the built-up list of warnings:
instance Warn (GenParser tok ([WarningReport], b)) where
  warnReport w = do (ws, other) <- getState
                    setState (ws ++ [w], other)

instance Die (GenParser tok st) where
  dieReport (Just m, err) = fail $ packMeta m err
  dieReport (Nothing, err) = fail err
--}}}

--{{{ matching rules for raw tokens
-- | Extract source position from a `Token`.
tokenPos :: Token -> SourcePos
tokenPos (m, _) = metaToSourcePos m

genToken :: (Token -> Maybe a) -> OccParser a
genToken test = token show tokenPos test

reserved :: String -> OccParser ()
reserved name = genToken test
  where
    test (_, TokReserved name')
        = if name' == name then Just () else Nothing
    test _ = Nothing

identifier :: OccParser String
identifier = genToken test
  where
    test (_, TokIdentifier s) = Just s
    test _ = Nothing

plainToken :: TokenType -> OccParser ()
plainToken t = genToken test
  where
    test (_, t') = if t == t' then Just () else Nothing
--}}}
--{{{ symbols
sAmp, sAssign, sBang, sBar, sColon, sColons, sComma, sEq, sLeft, sLeftR,
  sQuest, sRight, sRightR, sSemi
    :: OccParser ()

sAmp = reserved "&"
sAssign = reserved ":="
sBang = reserved "!"
sBar = reserved "|"
sColon = reserved ":"
sColons = reserved "::"
sComma = reserved ","
sEq = reserved "="
sLeft = reserved "["
sLeftR = reserved "("
sQuest = reserved "?"
sRight = reserved "]"
sRightR = reserved ")"
sSemi = reserved ";"
--}}}
--{{{ keywords
sAFTER, sALT, sAND, sANY, sAT, sBITAND, sBITNOT, sBITOR, sBOOL, sBYTE,
  sBYTESIN, sCASE, sCHAN, sDATA, sELSE, sFALSE, sFOR, sFROM, sFUNCTION, sIF,
  sINLINE, sIN, sINITIAL, sINT, sINT16, sINT32, sINT64, sIS, sMINUS, sMOSTNEG,
  sMOSTPOS, sNOT, sOF, sOFFSETOF, sOR, sPACKED, sPAR, sPLACE, sPLACED, sPLUS,
  sPORT, sPRI, sPROC, sPROCESSOR, sPROTOCOL, sREAL32, sREAL64, sRECORD, sREM,
  sRESHAPES, sRESULT, sRETYPES, sROUND, sSEQ, sSIZE, sSKIP, sSTOP, sTIMER,
  sTIMES, sTRUE, sTRUNC, sTYPE, sVAL, sVALOF, sWHILE, sWORKSPACE, sVECSPACE
    :: OccParser ()

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
sINLINE = reserved "INLINE"
sIN = reserved "IN"
sINITIAL = reserved "INITIAL"
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
sWORKSPACE = reserved "WORKSPACE"
sVECSPACE = reserved "VECSPACE"
--}}}
--{{{ markers inserted by the preprocessor
indent, outdent, eol :: OccParser ()

indent = do { plainToken Indent } <?> "indentation increase"
outdent = do { plainToken Outdent } <?> "indentation decrease"
eol = do { plainToken EndOfLine } <?> "end of line"
--}}}

--{{{ helper functions
md :: OccParser Meta
md
  =  do pos <- getPosition
        return $ sourcePosToMeta pos

--{{{ try*
-- These functions let you try a sequence of productions and only retrieve the
-- results from some of them. In the function name, X represents a value
-- that'll be thrown away, and V one that'll be kept; you get back a tuple of
-- the values you wanted.
--
-- There isn't anything particularly unusual going on here; it's just a more
-- succinct way of writing a try (do { ... }) expression.

tryXX :: OccParser a -> OccParser b -> OccParser ()
tryXX a b = try (do { a; b; return () })

tryXV :: OccParser a -> OccParser b -> OccParser b
tryXV a b = try (do { a; b })

tryVX :: OccParser a -> OccParser b -> OccParser a
tryVX a b = try (do { av <- a; b; return av })

tryVV :: OccParser a -> OccParser b -> OccParser (a, b)
tryVV a b = try (do { av <- a; bv <- b; return (av, bv) })

tryXXV :: OccParser a -> OccParser b -> OccParser c -> OccParser c
tryXXV a b c = try (do { a; b; cv <- c; return cv })

tryXVX :: OccParser a -> OccParser b -> OccParser c -> OccParser b
tryXVX a b c = try (do { a; bv <- b; c; return bv })

tryXVV :: OccParser a -> OccParser b -> OccParser c -> OccParser (b, c)
tryXVV a b c = try (do { a; bv <- b; cv <- c; return (bv, cv) })

tryVXX :: OccParser a -> OccParser b -> OccParser c -> OccParser a
tryVXX a b c = try (do { av <- a; b; c; return av })

tryVXV :: OccParser a -> OccParser b -> OccParser c -> OccParser (a, c)
tryVXV a b c = try (do { av <- a; b; cv <- c; return (av, cv) })

tryVVX :: OccParser a -> OccParser b -> OccParser c -> OccParser (a, b)
tryVVX a b c = try (do { av <- a; bv <- b; c; return (av, bv) })

tryXVXV :: OccParser a -> OccParser b -> OccParser c -> OccParser d -> OccParser (b, d)
tryXVXV a b c d = try (do { a; bv <- b; c; dv <- d; return (bv, dv) })

tryXVVX :: OccParser a -> OccParser b -> OccParser c -> OccParser d -> OccParser (b, c)
tryXVVX a b c d = try (do { a; bv <- b; cv <- c; d; return (bv, cv) })

tryVXXV :: OccParser a -> OccParser b -> OccParser c -> OccParser d -> OccParser (a, d)
tryVXXV a b c d = try (do { av <- a; b; c; dv <- d; return (av, dv) })

tryVXVX :: OccParser a -> OccParser b -> OccParser c -> OccParser d -> OccParser (a, c)
tryVXVX a b c d = try (do { av <- a; b; cv <- c; d; return (av, cv) })

tryVVXX :: OccParser a -> OccParser b -> OccParser c -> OccParser d -> OccParser (a, b)
tryVVXX a b c d = try (do { av <- a; bv <- b; c; d; return (av, bv) })

tryVVXV :: OccParser a -> OccParser b -> OccParser c -> OccParser d -> OccParser (a, b, d)
tryVVXV a b c d = try (do { av <- a; bv <- b; c; dv <- d; return (av, bv, dv) })
--}}}

--{{{ subscripts
maybeSubscripted :: String -> OccParser a -> (Meta -> A.Subscript -> a -> a) -> OccParser a
maybeSubscripted prodName inner subscripter
    =  do m <- md
          v <- inner
          subs <- many postSubscript
          return $ foldl (\var sub -> subscripter m sub var) v subs
    <?> prodName

postSubscript :: OccParser A.Subscript
postSubscript
    -- AMBIGUITY: in [x], x may be a variable or a field name.
    =   do m <- md
           e <- tryXV sLeft expression
           sRight
           return $ A.Subscript m A.CheckBoth e
    <|> do m <- md
           f <- tryXV sLeft fieldName
           sRight
           return $ A.SubscriptField m f
    <?> "subscript"

maybeSliced :: OccParser a -> (Meta -> A.Subscript -> a -> a) -> OccParser a
maybeSliced inner subscripter
    =  do m <- md

          (v, ff1) <- tryXVV sLeft inner fromOrFor

          e <- expression
          sub <- case ff1 of
                   "FROM" ->
                     (do f <- tryXV sFOR expression
                         sRight
                         return $ A.SubscriptFromFor m A.CheckBoth e f)
                     <|>
                     (do sRight
                         return $ A.SubscriptFrom m A.CheckBoth e)
                   "FOR" ->
                     do sRight
                        return $ A.SubscriptFor m A.CheckBoth e

          return $ subscripter m sub v
  where
    fromOrFor :: OccParser String
    fromOrFor = (sFROM >> return "FROM") <|> (sFOR >> return "FOR")
--}}}

-- | Parse an optional indented list, where if it's not there we should issue a
-- warning. (This is for things that are legal in the occam spec, but are
-- almost certainly programmer errors.)
maybeIndentedList :: Meta -> String -> OccParser t -> OccParser [t]
maybeIndentedList m msg inner
    =   do try indent
           vs <- many1 inner
           outdent
           return vs
    <|> do addWarning m msg
           return []

handleSpecs :: OccParser [A.Specification] -> OccParser a -> (Meta -> A.Specification -> a -> a) -> OccParser a
handleSpecs specs inner specMarker
    =   do m <- md
           ss <- specs
           ss' <- mapM scopeInSpec ss
           v <- inner
           mapM scopeOutSpec ss'
           return $ foldl (\e s -> specMarker m s e) v ss'

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

--}}}

--{{{ name scoping
findName :: A.Name -> OccParser A.Name
findName thisN
    =  do st <- get
          origN <- case lookup (A.nameName thisN) (csLocalNames st) of
                     Nothing -> dieP (A.nameMeta thisN) $ "name " ++ A.nameName thisN ++ " not defined"
                     Just n -> return n
          if A.nameType thisN /= A.nameType origN
            then dieP (A.nameMeta thisN) $ "expected " ++ show (A.nameType thisN) ++ " (" ++ A.nameName origN ++ " is " ++ show (A.nameType origN) ++ ")"
            else return $ thisN { A.nameName = A.nameName origN }

scopeIn :: A.Name -> A.SpecType -> A.AbbrevMode -> OccParser A.Name
scopeIn n@(A.Name m nt s) specType am
    =  do st <- getState
          s' <- makeUniqueName s
          let n' = n { A.nameName = s' }
          let nd = A.NameDef {
            A.ndMeta = m,
            A.ndName = s',
            A.ndOrigName = s,
            A.ndNameType = A.nameType n',
            A.ndSpecType = specType,
            A.ndAbbrevMode = am,
            A.ndPlacement = A.Unplaced
          }
          defineName n' nd
          modify $ (\st -> st {
                             csLocalNames = (s, n') : (csLocalNames st)
                           })
          return n'

scopeOut :: A.Name -> OccParser ()
scopeOut n@(A.Name m nt s)
    =  do st <- get
          let lns' = case csLocalNames st of
                       (s, _):ns -> ns
                       otherwise -> dieInternal (Just m, "scopeOut trying to scope out the wrong name")
          put $ st { csLocalNames = lns' }

scopeInRep :: A.Replicator -> OccParser A.Replicator
scopeInRep (A.For m n b c)
    =  do n' <- scopeIn n (A.Declaration m A.Int) A.ValAbbrev
          return $ A.For m n' b c

scopeOutRep :: A.Replicator -> OccParser ()
scopeOutRep (A.For m n b c) = scopeOut n

scopeInSpec :: A.Specification -> OccParser A.Specification
scopeInSpec (A.Specification m n st)
    =  do n' <- scopeIn n st (abbrevModeOfSpec st)
          return $ A.Specification m n' st

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
--
-- Productions with an "-- AMBIGUITY" comment match something that's ambiguous
-- in the occam grammar, and may thus produce incorrect AST fragments. The
-- ambiguities will be resolved later.

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

channelName, dataTypeName, functionName, portName, procName, protocolName,
  recordName, timerName, variableName
    :: OccParser A.Name

channelName = name A.ChannelName
dataTypeName = name A.DataTypeName
functionName = name A.FunctionName
portName = name A.PortName
procName = name A.ProcName
protocolName = name A.ProtocolName
recordName = name A.RecordName
timerName = name A.TimerName
variableName = name A.VariableName

newChannelName, newDataTypeName, newFunctionName, newPortName, newProcName, newProtocolName,
  newRecordName, newTimerName, newVariableName
    :: OccParser A.Name

newChannelName = newName A.ChannelName
newDataTypeName = newName A.DataTypeName
newFunctionName = newName A.FunctionName
newPortName = newName A.PortName
newProcName = newName A.ProcName
newProtocolName = newName A.ProtocolName
newRecordName = newName A.RecordName
newTimerName = newName A.TimerName
newVariableName = newName A.VariableName

-- | A name that isn't scoped.
-- This is for things like record fields: we don't need to track their scope
-- because they're only valid with the particular record they're defined in,
-- but we do need to add a unique suffix so that they don't collide with
-- keywords in the target language
unscopedName :: A.NameType -> OccParser A.Name
unscopedName nt
    =  do n <- anyName nt
          findUnscopedName n
    <?> show nt

fieldName, tagName, newFieldName, newTagName :: OccParser A.Name

fieldName = unscopedName A.FieldName
tagName = unscopedName A.TagName
newFieldName = unscopedName A.FieldName
newTagName = unscopedName A.TagName
--}}}
--{{{ types
-- | A sized array of a production.
arrayType :: OccParser A.Type -> OccParser A.Type
arrayType element
    =  do (s, t) <- tryXVXV sLeft expression sRight element
          return $ addDimensions [A.Dimension s] t

-- | Either a sized or unsized array of a production.
specArrayType :: OccParser A.Type -> OccParser A.Type
specArrayType element
    =   arrayType element
    <|> do t <- tryXXV sLeft sRight element
           return $ addDimensions [A.UnknownDimension] t

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
    <|> arrayType dataType
    <|> do { n <- try dataTypeName; return $ A.UserDataType n }
    <|> do { n <- try recordName; return $ A.Record n }
    <?> "data type"

channelType :: OccParser A.Type
channelType
    =   do { sCHAN; optional sOF; p <- protocol; return $ A.Chan A.DirUnknown A.ChanAttributes {A.caWritingShared = False, A.caReadingShared = False} p }
    <|> arrayType channelType
    <?> "channel type"

timerType :: OccParser A.Type
timerType
    =   do { sTIMER; return $ A.Timer A.OccamTimer }
    <|> arrayType timerType
    <?> "timer type"

portType :: OccParser A.Type
portType
    =   do { sPORT; sOF; p <- dataType; return $ A.Port p }
    <|> arrayType portType
    <?> "port type"
--}}}
--{{{ literals

typeDecorator :: OccParser A.Type
typeDecorator
    =   do sLeftR
           t <- dataType
           sRightR
           return t
    <|> return A.Infer
    <?> "literal type decorator"

literal :: OccParser A.Expression
literal
    =  do m <- md
          lr <- untypedLiteral
          t <- typeDecorator
          return $ A.Literal m t lr
    <?> "literal"

untypedLiteral :: OccParser A.LiteralRepr
untypedLiteral
    =   real
    <|> integer
    <|> byte

real :: OccParser A.LiteralRepr
real
    =   do m <- md
           genToken (test m)
    <?> "real literal"
  where
    test m (_, TokRealLiteral s) = Just $ A.RealLiteral m s
    test _ _ = Nothing

integer :: OccParser A.LiteralRepr
integer
    =  do m <- md
          genToken (test m)
    <?> "integer literal"
  where
    test m (_, TokIntLiteral s) = Just $ A.IntLiteral m s
    test m (_, TokHexLiteral s) = Just $ A.HexLiteral m (drop 1 s)
    test _ _ = Nothing

byte :: OccParser A.LiteralRepr
byte
    =  do m <- md
          genToken (test m)
    <?> "byte literal"
  where
    test m (_, TokCharLiteral s)
        = case splitStringLiteral m (chop 1 1 s) of [lr] -> Just lr
    test _ _ = Nothing

-- | Parse a table -- an array literal which might be subscripted or sliced.
-- (The implication of this is that the type of the expression this parses
-- isn't necessarily an array type -- it might be something like
-- @[1, 2, 3][1]@.)
-- The expression this returns cannot be used directly; it doesn't have array
-- literals collapsed, and record literals are array literals of type []ANY.
table :: OccParser A.Expression
table
    = maybeSubscripted "table" table' A.SubscriptedExpr

table' :: OccParser A.Expression
table'
    =   do m <- md
           (defT, lr) <- tableElems
           t <- typeDecorator
           let t' = case t of
                      A.Infer -> defT
                      _ -> t
           return $ A.Literal m t' lr
    <|> maybeSliced table A.SubscriptedExpr
    <?> "table'"

tableElems :: OccParser (A.Type, A.LiteralRepr)
tableElems
    =   stringLiteral
    <|> do m <- md
           es <- tryXVX sLeft (sepBy1 expression sComma) sRight
           return (A.Infer, A.ArrayLiteral m (map A.ArrayElemExpr es))
    <?> "table elements"

-- String literals are implicitly typed []BYTE unless otherwise specified, so
-- we can tell the type of "".
stringLiteral :: OccParser (A.Type, A.LiteralRepr)
stringLiteral
    =  do m <- md
          cs <- stringCont <|> stringLit
          let aes = [A.ArrayElemExpr $ A.Literal m' A.Infer c
                     | c@(A.ByteLiteral m' _) <- cs]
          return (A.Array [A.UnknownDimension] A.Byte, A.ArrayLiteral m aes)
    <?> "string literal"
  where
    stringCont :: OccParser [A.LiteralRepr]
    stringCont
        =  do m <- md
              s <- genToken test
              rest <- stringCont <|> stringLit
              return $ (splitStringLiteral m s) ++ rest
      where
        test (_, TokStringCont s) = Just (chop 1 2 s)
        test _ = Nothing

    stringLit :: OccParser [A.LiteralRepr]
    stringLit
        =  do m <- md
              s <- genToken test
              return $ splitStringLiteral m s
      where
        test (_, TokStringLiteral s) = Just (chop 1 1 s)
        test _ = Nothing

-- | Parse a string literal.
-- FIXME: This should decode the occam escapes.
splitStringLiteral :: Meta -> String -> [A.LiteralRepr]
splitStringLiteral m cs = ssl cs
  where
    ssl [] = []
    ssl ('*':'#':a:b:cs)
        = (A.ByteLiteral m ['*', '#', a, b]) : ssl cs
    ssl ('*':'\n':cs)
        = (A.ByteLiteral m $ tail $ dropWhile (/= '*') cs) : ssl cs
    ssl ('*':c:cs)
        = (A.ByteLiteral m ['*', c]) : ssl cs
    ssl (c:cs)
        = (A.ByteLiteral m [c]) : ssl cs
--}}}
--{{{ expressions
expressionList :: OccParser A.ExpressionList
expressionList
    -- AMBIGUITY: this will also match FunctionCallList.
    =   do m <- md
           es <- sepBy1 expression sComma
           return $ A.ExpressionList m es
-- XXX: Value processes are not supported (because nobody uses them and they're hard to parse)
    <?> "expression list"

expression :: OccParser A.Expression
expression
    =   do m <- md
           o <- monadicOperator
           v <- operand
           return $ A.Monadic m o v
    <|> do { m <- md; sMOSTPOS; t <- dataType; return $ A.MostPos m t }
    <|> do { m <- md; sMOSTNEG; t <- dataType; return $ A.MostNeg m t }
    <|> sizeExpr
    <|> do m <- md
           (l, o) <- tryVV operand dyadicOperator
           r <- operand
           return $ A.Dyadic m o l r
    <|> associativeOpExpression
    <|> conversion
    <|> operand
    <?> "expression"

arrayConstructor :: OccParser A.Expression
arrayConstructor
    =  do m <- md
          sLeft
          r <- replicator
          sBar
          r' <- scopeInRep r
          e <- expression
          scopeOutRep r'
          sRight
          return $ A.ExprConstr m $ A.RepConstr m A.Infer r' e
    <?> "array constructor expression"

associativeOpExpression :: OccParser A.Expression
associativeOpExpression
    =  do m <- md
          (l, o) <- tryVV operand associativeOperator
          r <- associativeOpExpression <|> operand
          return $ A.Dyadic m o l r
    <?> "associative operator expression"

sizeExpr :: OccParser A.Expression
sizeExpr
    =  do m <- md
          sSIZE
          do { t <- dataType; return $ A.SizeType m t }
            <|> do v <- operand
                   return $ A.SizeExpr m v
            <|> do v <- (channel <|> timer <|> port)
                   return $ A.SizeVariable m v
    <?> "SIZE expression"

functionCall :: OccParser A.Expression
functionCall
    =   do m <- md
           n <- tryVX functionName sLeftR
           as <- sepBy expression sComma
           sRightR
           return $ A.FunctionCall m n as
    <|> do m <- md
           s <- tryVX intrinsicFunctionName sLeftR
           as <- sepBy expression sComma
           sRightR
           return $ A.IntrinsicFunctionCall m s as
    <?> "function call"
  where
    intrinsicFunctionName :: OccParser String
    intrinsicFunctionName
        =  do s <- anyName A.FunctionName >>* A.nameName
              case lookup s intrinsicFunctions of
                Just _ -> return s
                Nothing -> pzero

monadicOperator :: OccParser A.MonadicOp
monadicOperator
    =   do { reserved "-"; return A.MonadicSubtr }
    <|> do { sMINUS; return A.MonadicMinus }
    <|> do { reserved "~" <|> sBITNOT; return A.MonadicBitNot }
    <|> do { sNOT; return A.MonadicNot }
    <?> "monadic operator"

dyadicOperator :: OccParser A.DyadicOp
dyadicOperator
    =   do { reserved "+"; return A.Add }
    <|> do { reserved "-"; return A.Subtr }
    <|> do { reserved "*"; return A.Mul }
    <|> do { reserved "/"; return A.Div }
    <|> do { reserved "\\"; return A.Rem }
    <|> do { sREM; return A.Rem }
    <|> do { sMINUS; return A.Minus }
    <|> do { reserved "/\\" <|> sBITAND; return A.BitAnd }
    <|> do { reserved "\\/" <|> sBITOR; return A.BitOr }
    <|> do { reserved "><"; return A.BitXor }
    <|> do { reserved "<<"; return A.LeftShift }
    <|> do { reserved ">>"; return A.RightShift }
    <|> do { reserved "="; return A.Eq }
    <|> do { reserved "<>"; return A.NotEq }
    <|> do { reserved "<"; return A.Less }
    <|> do { reserved ">"; return A.More }
    <|> do { reserved "<="; return A.LessEq }
    <|> do { reserved ">="; return A.MoreEq }
    <|> do { sAFTER; return A.After }
    <?> "dyadic operator"

associativeOperator :: OccParser A.DyadicOp
associativeOperator
    =   do { sAND; return A.And }
    <|> do { sOR; return A.Or }
    <|> do { sPLUS; return A.Plus }
    <|> do { sTIMES; return A.Times }
    <?> "associative operator"

conversion :: OccParser A.Expression
conversion
    =  do m <- md
          t <- dataType
          (c, o) <- conversionMode
          return $ A.Conversion m c t o
    <?> "conversion"

conversionMode :: OccParser (A.ConversionMode, A.Expression)
conversionMode
    =   do { sROUND; o <- operand; return (A.Round, o) }
    <|> do { sTRUNC; o <- operand; return (A.Trunc, o) }
    <|> do { o <- operand; return (A.DefaultConversion, o) }
    <?> "conversion mode and operand"
--}}}
--{{{ operands
operand :: OccParser A.Expression
operand
    = maybeSubscripted "operand" operand' A.SubscriptedExpr

operand' :: OccParser A.Expression
operand'
    =   do { m <- md; v <- variable; return $ A.ExprVariable m v }
    <|> literal
    <|> do { sLeftR; e <- expression; sRightR; return e }
-- XXX value process
    <|> functionCall
    <|> do m <- md
           sBYTESIN
           sLeftR
           (try (do { o <- operand; sRightR; return $ A.BytesInExpr m o }))
             <|> do { t <- dataType; sRightR; return $ A.BytesInType m t }
    <|> do { m <- md; sOFFSETOF; sLeftR; t <- dataType; sComma; f <- fieldName; sRightR; return $ A.OffsetOf m t f }
    <|> do { m <- md; sTRUE; return $ A.True m }
    <|> do { m <- md; sFALSE; return $ A.False m }
    <|> table
    <|> arrayConstructor
    <?> "operand"
--}}}
--{{{ variables, channels, timers, ports
variable :: OccParser A.Variable
variable
    = maybeSubscripted "variable" variable' A.SubscriptedVariable

variable' :: OccParser A.Variable
variable'
    =   do { m <- md; n <- try variableName; return $ A.Variable m n }
    <|> maybeSliced variable A.SubscriptedVariable
    <?> "variable'"

channel :: OccParser A.Variable
channel
    =   maybeSubscripted "channel" channel' A.SubscriptedVariable
    <?> "channel"

channel' :: OccParser A.Variable
channel'
    =   do { m <- md; n <- try channelName; return $ A.Variable m n }
    <|> maybeSliced channel A.SubscriptedVariable
    <?> "channel'"

timer :: OccParser A.Variable
timer
    =   maybeSubscripted "timer" timer' A.SubscriptedVariable
    <?> "timer"

timer' :: OccParser A.Variable
timer'
    =   do { m <- md; n <- try timerName; return $ A.Variable m n }
    <|> maybeSliced timer A.SubscriptedVariable
    <?> "timer'"

port :: OccParser A.Variable
port
    =   maybeSubscripted "port" port' A.SubscriptedVariable
    <?> "port"

port' :: OccParser A.Variable
port'
    =   do { m <- md; n <- try portName; return $ A.Variable m n }
    <|> maybeSliced port A.SubscriptedVariable
    <?> "port'"
--}}}
--{{{ protocols
protocol :: OccParser A.Type
protocol
    =   do { n <- try protocolName ; return $ A.UserProtocol n }
    <|> simpleProtocol
    <?> "protocol"

simpleProtocol :: OccParser A.Type
simpleProtocol
    =   do { l <- tryVX dataType sColons; sLeft; sRight; r <- dataType; return $ A.Counted l (addDimensions [A.UnknownDimension] r) }
    <|> dataType
    <|> do { sANY; return $ A.Any }
    <?> "simple protocol"

sequentialProtocol :: OccParser [A.Type]
sequentialProtocol
    =   do { l <- try $ sepBy1 simpleProtocol sSemi; return l }
    <?> "sequential protocol"

taggedProtocol :: OccParser (A.Name, [A.Type])
taggedProtocol
    =   do { t <- tryVX newTagName eol; return (t, []) }
    <|> do { t <- newTagName; sSemi; sp <- sequentialProtocol; eol; return (t, sp) }
    <?> "tagged protocol"
--}}}
--{{{ replicators
replicator :: OccParser A.Replicator
replicator
    =  do m <- md
          n <- tryVX newVariableName sEq
          b <- expression
          sFOR
          c <- expression
          return $ A.For m n b c
    <?> "replicator"
--}}}
--{{{ specifications, declarations, allocations
allocation :: OccParser [A.Specification]
allocation
    =   do m <- md
           sPLACE
           n <- try variableName <|> try channelName <|> portName
           p <- placement
           sColon
           eol
           nd <- lookupNameOrError n $ dieP m ("Attempted to PLACE unknown variable: " ++ (show $ A.nameName n))
           defineName n $ nd { A.ndPlacement = p }
           return []
    <?> "allocation"

placement :: OccParser A.Placement
placement
    =   do e <- tryXV (optional sAT) expression
           return $ A.PlaceAt e
    <|> do tryXX sIN sWORKSPACE
           return $ A.PlaceInWorkspace
    <|> do tryXX sIN sVECSPACE
           return $ A.PlaceInVecspace
    <?> "placement"

specification :: OccParser [A.Specification]
specification
    =   do { m <- md; (ns, d) <- declaration; return [A.Specification m n d | n <- ns] }
    <|> do { a <- abbreviation; return [a] }
    <|> do { d <- definition; return [d] }
    <?> "specification"

declaration :: OccParser ([A.Name], A.SpecType)
declaration
    =   declOf dataType newVariableName
    <|> declOf channelType newChannelName
    <|> declOf timerType newTimerName
    <|> declOf portType newPortName
    <?> "declaration"

declOf :: OccParser A.Type -> OccParser A.Name -> OccParser ([A.Name], A.SpecType)
declOf spec newName
    =  do m <- md
          (d, ns) <- tryVVX spec (sepBy1 newName sComma) sColon
          eol
          return (ns, A.Declaration m d)

abbreviation :: OccParser A.Specification
abbreviation
    =   valIsAbbrev
    <|> initialIsAbbrev
    <|> isAbbrev newVariableName variable
    <|> isAbbrev newChannelName channel
    <|> chanArrayAbbrev
    <|> isAbbrev newTimerName timer
    <|> isAbbrev newPortName port
    <?> "abbreviation"

valIsAbbrev :: OccParser A.Specification
valIsAbbrev
    =  do m <- md
          (n, t, e) <- do { n <- tryXVX sVAL newVariableName sIS; e <- expression; sColon; eol; return (n, A.Infer, e) }
                       <|> do { (s, n) <- tryXVVX sVAL dataSpecifier newVariableName sIS; e <- expression; sColon; eol; return (n, s, e) }
          return $ A.Specification m n $ A.IsExpr m A.ValAbbrev t e
    <?> "VAL IS abbreviation"

initialIsAbbrev :: OccParser A.Specification
initialIsAbbrev
    =   do m <- md
           (t, n) <- tryXVVX sINITIAL dataSpecifier newVariableName sIS
           e <- expression
           sColon
           eol
           return $ A.Specification m n $ A.IsExpr m A.Original t e
    <?> "INITIAL IS abbreviation"

isAbbrev :: OccParser A.Name -> OccParser A.Variable -> OccParser A.Specification
isAbbrev newName oldVar
    =   do m <- md
           (n, v) <- tryVXV newName sIS oldVar
           sColon
           eol
           return $ A.Specification m n $ A.Is m A.Abbrev A.Infer v
    <|> do m <- md
           (s, n, v) <- tryVVXV specifier newName sIS oldVar
           sColon
           eol
           return $ A.Specification m n $ A.Is m A.Abbrev s v
    <?> "IS abbreviation"

chanArrayAbbrev :: OccParser A.Specification
chanArrayAbbrev
    =   do m <- md
           (n, cs) <- tryVXXV newChannelName sIS sLeft (sepBy1 channel sComma)
           sRight
           sColon
           eol
           return $ A.Specification m n $ A.IsChannelArray m A.Infer cs
    <|> do m <- md
           (s, n) <- tryVVXX channelSpecifier newChannelName sIS sLeft
           cs <- sepBy1 channel sComma
           sRight
           sColon
           eol
           return $ A.Specification m n $ A.IsChannelArray m s cs
    <?> "channel array abbreviation"

specMode :: OccParser () -> OccParser A.SpecMode
specMode keyword
    =   do tryXX sINLINE keyword
           return A.InlineSpec
    <|> do keyword
           return A.PlainSpec
    <?> "specification mode"

definition :: OccParser A.Specification
definition
    =   do m <- md
           sDATA
           sTYPE
           do { n <- tryVX newDataTypeName sIS; t <- dataType; sColon; eol; return $ A.Specification m n (A.DataType m t) }
             <|> do { n <- newRecordName; eol; indent; rec <- structuredType; outdent; sColon; eol; return $ A.Specification m n rec }
    <|> do m <- md
           sPROTOCOL
           n <- newProtocolName
           do { sIS; p <- sequentialProtocol; sColon; eol; return $ A.Specification m n $ A.Protocol m p }
             <|> do { eol; indent; sCASE; eol; ps <- maybeIndentedList m "empty CASE protocol" taggedProtocol; outdent; sColon; eol; return $ A.Specification m n $ A.ProtocolCase m ps }
    <|> do m <- md
           sm <- specMode sPROC
           n <- newProcName
           fs <- formalList
           eol
           indent
           fs' <- scopeInFormals fs
           p <- process
           scopeOutFormals fs'
           outdent
           sColon
           eol
           return $ A.Specification m n $ A.Proc m sm fs' p
    <|> do m <- md
           (rs, sm) <- tryVV (sepBy1 dataType sComma) (specMode sFUNCTION)
           n <- newFunctionName
           fs <- formalList
           do { sIS; fs' <- scopeInFormals fs; el <- expressionList; scopeOutFormals fs'; sColon; eol; return $ A.Specification m n $ A.Function m sm rs fs' (Left $ A.Only m el) }
             <|> do { eol; indent; fs' <- scopeInFormals fs; vp <- valueProcess; scopeOutFormals fs'; outdent; sColon; eol; return $ A.Specification m n $ A.Function m sm rs fs' (Left vp) }
    <|> retypesAbbrev
    <?> "definition"

retypesReshapes :: OccParser ()
retypesReshapes
    = sRETYPES <|> sRESHAPES

-- FIXME: Retypes checking is currently disabled; it will be moved into a
-- separate pass.
retypesAbbrev :: OccParser A.Specification
retypesAbbrev
    =   do m <- md
           (s, n) <- tryVVX dataSpecifier newVariableName retypesReshapes
           v <- variable
           sColon
           eol
           return $ A.Specification m n $ A.Retypes m A.Abbrev s v
    <|> do m <- md
           (s, n) <- tryVVX channelSpecifier newChannelName retypesReshapes
           c <- channel
           sColon
           eol
           return $ A.Specification m n $ A.Retypes m A.Abbrev s c
    <|> do m <- md
           (s, n) <- tryXVVX sVAL dataSpecifier newVariableName retypesReshapes
           e <- expression
           sColon
           eol
           return $ A.Specification m n $ A.RetypesExpr m A.ValAbbrev s e
    <?> "RETYPES/RESHAPES abbreviation"

dataSpecifier :: OccParser A.Type
dataSpecifier
    =   dataType
    <|> specArrayType dataSpecifier
    <?> "data specifier"

channelSpecifier :: OccParser A.Type
channelSpecifier
    =   channelType
    <|> specArrayType channelSpecifier
    <?> "channel specifier"

timerSpecifier :: OccParser A.Type
timerSpecifier
    =   timerType
    <|> specArrayType timerSpecifier
    <?> "timer specifier"

portSpecifier :: OccParser A.Type
portSpecifier
    =   portType
    <|> specArrayType portSpecifier
    <?> "port specifier"

specifier :: OccParser A.Type
specifier
    =   dataType
    <|> channelType
    <|> timerType
    <|> portType
    <|> specArrayType specifier
    <?> "specifier"

--{{{ PROCs and FUNCTIONs
formalList :: OccParser [A.Formal]
formalList
    =  do m <- md
          sLeftR
          fs <- option [] formalArgSet
          sRightR
          return fs
    <?> "formal list"

formalItem :: OccParser (A.AbbrevMode, A.Type) -> OccParser A.Name -> OccParser [A.Formal]
formalItem spec name
    =   do (am, t) <- spec
           names am t
  where
    names :: A.AbbrevMode -> A.Type -> OccParser [A.Formal]
    names am t
        = do n <- name
             fs <- tail am t
             return $ (A.Formal am t n) : fs

    tail :: A.AbbrevMode -> A.Type -> OccParser [A.Formal]
    tail am t
        =   do sComma
               -- We must try formalArgSet first here, so that we don't
               -- accidentally parse a DATA TYPE name thinking it's a formal
               -- name.
               formalArgSet <|> names am t
        <|> return []

-- | Parse a set of formal arguments.
formalArgSet :: OccParser [A.Formal]
formalArgSet
    =   formalItem formalVariableType newVariableName
    <|> formalItem (aa channelSpecifier) newChannelName
    <|> formalItem (aa timerSpecifier) newTimerName
    <|> formalItem (aa portSpecifier) newPortName
  where
    aa :: OccParser A.Type -> OccParser (A.AbbrevMode, A.Type)
    aa = liftM (\t -> (A.Abbrev, t))

formalVariableType :: OccParser (A.AbbrevMode, A.Type)
formalVariableType
    =   do sVAL
           s <- dataSpecifier
           return (A.ValAbbrev, s)
    <|> do s <- dataSpecifier
           return (A.Abbrev, s)
    <?> "formal variable type"

valueProcess :: OccParser (A.Structured A.ExpressionList)
valueProcess
    =   do m <- md
           sVALOF
           eol
           indent
           p <- process
           sRESULT
           el <- expressionList
           eol
           outdent
           return $ A.ProcThen m p (A.Only m el)
    <|> handleSpecs specification valueProcess A.Spec
    <?> "value process"
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
           return $ A.RecordType m isPacked (concat fs)
    <?> "structured type"

recordKeyword :: OccParser Bool
recordKeyword
    =   do { sPACKED; sRECORD; return True }
    <|> do { sRECORD; return False }

structuredTypeField :: OccParser [(A.Name, A.Type)]
structuredTypeField
    =   do t <- dataType
           fs <- sepBy1 newFieldName sComma
           sColon
           eol
           return [(f, t) | f <- fs]
    <?> "structured type field"
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
    <|> intrinsicProc
    <|> handleSpecs (allocation <|> specification) process
                    (\m s p -> A.Seq m (A.Spec m s (A.Only m p)))
    <?> "process"

--{{{ assignment (:=)
assignment :: OccParser A.Process
assignment
    =   do m <- md
           vs <- tryVX (sepBy1 variable sComma) sAssign
           es <- expressionList
           eol
           return $ A.Assign m vs es
    <?> "assignment"
--}}}
--{{{ input (?)
inputProcess :: OccParser A.Process
inputProcess
    =   do m <- md
           (c, i) <- input
           return $ A.Input m c i
    <?> "input process"

input :: OccParser (A.Variable, A.InputMode)
input
    =   channelInput
    <|> timerInput
    <|> do m <- md
           p <- tryVX port sQuest
           v <- variable
           eol
           return (p, A.InputSimple m [A.InVariable m v])
    <?> "input"

channelInput :: OccParser (A.Variable, A.InputMode)
channelInput
    =   do m <- md
           c <- tryVX channel sQuest
           caseInput m c <|> plainInput m c
    <?> "channel input"
  where
    caseInput m c
        = do sCASE
             tl <- taggedList
             eol
             return (c, A.InputCase m (A.Only m (tl (A.Skip m))))
    plainInput m c
        = do is <- sepBy1 inputItem sSemi
             eol
             return (c, A.InputSimple m is)

timerInput :: OccParser (A.Variable, A.InputMode)
timerInput
    =   do m <- md
           c <- tryVX timer sQuest
           do { v <- variable; eol; return (c, A.InputTimerRead m (A.InVariable m v)) }
             <|> do { sAFTER; e <- expression; eol; return (c, A.InputTimerAfter m e) }
    <?> "timer input"

taggedList :: OccParser (A.Process -> A.Variant)
taggedList
    =  do m <- md
          tag <- tagName
          is <- many (sSemi >> inputItem)
          return $ A.Variant m tag is
    <?> "tagged list"

inputItem :: OccParser A.InputItem
inputItem
    =   do m <- md
           v <- tryVX variable sColons
           w <- variable
           return $ A.InCounted m v w
    <|> do m <- md
           v <- variable
           return $ A.InVariable m v
    <?> "input item"
--}}}
--{{{ variant input (? CASE)
caseInput :: OccParser A.Process
caseInput
    =   do m <- md
           c <- tryVX channel (sQuest >> sCASE >> eol)
           vs <- maybeIndentedList m "empty ? CASE" variant
           return $ A.Input m c (A.InputCase m (A.Several m vs))
    <?> "case input"

variant :: OccParser (A.Structured A.Variant)
variant
    =   do m <- md
           tl <- taggedList
           eol
           indent
           p <- process
           outdent
           return $ A.Only m (tl p)
    <|> handleSpecs specification variant A.Spec
    <?> "variant"
--}}}
--{{{ output (!)
output :: OccParser A.Process
output
    =   channelOutput
    <|> do m <- md
           p <- tryVX port sBang
           e <- expression
           eol
           return $ A.Output m p [A.OutExpression m e]
    <?> "output"

channelOutput :: OccParser A.Process
channelOutput
    =   do m <- md
           c <- tryVX channel sBang
           -- AMBIGUITY: in "a ! b", b may be a tag or a variable.
           regularOutput m c <|> caseOutput m c
    <?> "channel output"
  where
    regularOutput m c
        =  do o <- try outputItem
              os <- many (sSemi >> outputItem)
              eol
              return $ A.Output m c (o:os)
    caseOutput m c
        =  do tag <- tagName
              os <- many (sSemi >> outputItem)
              eol
              return $ A.OutputCase m c tag os

outputItem :: OccParser A.OutputItem
outputItem
    =   do m <- md
           a <- tryVX expression sColons
           b <- expression
           return $ A.OutCounted m a b
    <|> do m <- md
           e <- expression
           return $ A.OutExpression m e
    <?> "output item"
--}}}
--{{{ SEQ
seqProcess :: OccParser A.Process
seqProcess
    =   do m <- md
           sSEQ
           do { eol; ps <- maybeIndentedList m "empty SEQ" process; return $ A.Seq m (A.Several m (map (A.Only m) ps)) }
             <|> do { r <- replicator; eol; indent; r' <- scopeInRep r; p <- process; scopeOutRep r'; outdent; return $ A.Seq m (A.Rep m r' (A.Only m p)) }
    <?> "SEQ process"
--}}}
--{{{ IF
ifProcess :: OccParser A.Process
ifProcess
    =   do m <- md
           c <- conditional
           return $ A.If m c
    <?> "IF process"

conditional :: OccParser (A.Structured A.Choice)
conditional
    =   do m <- md
           sIF
           do { eol; cs <- maybeIndentedList m "empty IF" ifChoice; return $ A.Several m cs }
             <|> do { r <- replicator; eol; indent; r' <- scopeInRep r; c <- ifChoice; scopeOutRep r'; outdent; return $ A.Rep m r' c }
    <?> "conditional"

ifChoice :: OccParser (A.Structured A.Choice)
ifChoice
    =   guardedChoice
    <|> conditional
    <|> handleSpecs specification ifChoice A.Spec
    <?> "choice"

guardedChoice :: OccParser (A.Structured A.Choice)
guardedChoice
    =   do m <- md
           b <- expression
           eol
           indent
           p <- process
           outdent
           return $ A.Only m (A.Choice m b p)
    <?> "guarded choice"
--}}}
--{{{ CASE
caseProcess :: OccParser A.Process
caseProcess
    =   do m <- md
           sCASE
           sel <- expression
           eol
           os <- maybeIndentedList m "empty CASE" caseOption
           return $ A.Case m sel (A.Several m os)
    <?> "CASE process"

caseOption :: OccParser (A.Structured A.Option)
caseOption
    =   do m <- md
           ces <- tryVX (sepBy1 expression sComma) eol
           indent
           p <- process
           outdent
           return $ A.Only m (A.Option m ces p)
    <|> do m <- md
           sELSE
           eol
           indent
           p <- process
           outdent
           return $ A.Only m (A.Else m p)
    <|> handleSpecs specification caseOption A.Spec
    <?> "option"
--}}}
--{{{ WHILE
whileProcess :: OccParser A.Process
whileProcess
    =   do m <- md
           sWHILE
           b <- expression
           eol
           indent
           p <- process
           outdent
           return $ A.While m b p
    <?> "WHILE process"
--}}}
--{{{ PAR
parallel :: OccParser A.Process
parallel
    =   do m <- md
           isPri <- parKeyword
           do { eol; ps <- maybeIndentedList m "empty PAR" process; return $ A.Par m isPri (A.Several m (map (A.Only m) ps)) }
             <|> do { r <- replicator; eol; indent; r' <- scopeInRep r; p <- process; scopeOutRep r'; outdent; return $ A.Par m isPri (A.Rep m r' (A.Only m p)) }
    <|> processor
    <?> "PAR process"

parKeyword :: OccParser A.ParMode
parKeyword
    =   do { sPAR; return A.PlainPar }
    <|> do { tryXX sPRI sPAR; return A.PriPar }
    <|> do { tryXX sPLACED sPAR; return A.PlacedPar }

-- XXX PROCESSOR as a process isn't really legal, surely?
processor :: OccParser A.Process
processor
    =   do m <- md
           sPROCESSOR
           e <- expression
           eol
           indent
           p <- process
           outdent
           return $ A.Processor m e p
    <?> "PLACED PAR process"
--}}}
--{{{ ALT
altProcess :: OccParser A.Process
altProcess
    =   do m <- md
           (isPri, a) <- alternation
           return $ A.Alt m isPri a
    <?> "ALT process"

alternation :: OccParser (Bool, A.Structured A.Alternative)
alternation
    =   do m <- md
           isPri <- altKeyword
           do { eol; as <- maybeIndentedList m "empty ALT" alternative; return (isPri, A.Several m as) }
             <|> do { r <- replicator; eol; indent; r' <- scopeInRep r; a <- alternative; scopeOutRep r'; outdent; return (isPri, A.Rep m r' a) }
    <?> "alternation"

altKeyword :: OccParser Bool
altKeyword
    =   do { sALT; return False }
    <|> do { tryXX sPRI sALT; return True }

-- The reason the CASE guards end up here is because they have to be handled
-- specially: you can't tell until parsing the guts of the CASE what the processes
-- are.
alternative :: OccParser (A.Structured A.Alternative)
alternative
    -- FIXME: Check we don't have PRI ALT inside ALT.
    =   do (isPri, a) <- alternation
           return a
    -- These are special cases to deal with c ? CASE inside ALTs -- the normal
    -- guards are below.
    <|> do m <- md
           (b, c) <- tryVXVX expression sAmp channel (sQuest >> sCASE >> eol)
           vs <- maybeIndentedList m "empty ? CASE" variant
           return $ A.Only m (A.Alternative m b c (A.InputCase m $ A.Several m vs) (A.Skip m))
    <|> do m <- md
           c <- tryVXX channel sQuest (sCASE >> eol)
           vs <- maybeIndentedList m "empty ? CASE" variant
           return $ A.Only m (A.Alternative m (A.True m) c (A.InputCase m $ A.Several m vs) (A.Skip m))
    <|> guardedAlternative
    <|> handleSpecs specification alternative A.Spec
    <?> "alternative"

guardedAlternative :: OccParser (A.Structured A.Alternative)
guardedAlternative
    =   do m <- md
           makeAlt <- guard
           indent
           p <- process
           outdent
           return $ A.Only m (makeAlt p)
    <?> "guarded alternative"

guard :: OccParser (A.Process -> A.Alternative)
guard
    =   do m <- md
           (c, im) <- input
           return $ A.Alternative m (A.True m) c im
    <|> do m <- md
           b <- tryVX expression sAmp
           do { (c, im) <- input; return $ A.Alternative m b c im }
             <|> do { sSKIP; eol; return $ A.AlternativeSkip m b }
    <?> "guard"
--}}}
--{{{ PROC calls
-- FIXME: This shouldn't need to look at the definition
procInstance :: OccParser A.Process
procInstance
    =  do m <- md
          n <- tryVX procName sLeftR
          st <- specTypeOfName n
          let fs = case st of A.Proc _ _ fs _ -> fs
          as <- actuals fs
          sRightR
          eol
          return $ A.ProcCall m n as
    <?> "PROC instance"

actuals :: [A.Formal] -> OccParser [A.Actual]
actuals fs = intersperseP (map actual fs) sComma

actual :: A.Formal -> OccParser A.Actual
actual (A.Formal am t n)
    =  do case am of
            A.ValAbbrev -> expression >>* A.ActualExpression
            _ ->
              case stripArrayType t of
                A.Chan {} -> var channel
                A.Timer {} -> var timer
                A.Port _ -> var port
                _ -> var variable
    <?> "actual of type " ++ showOccam t ++ " for " ++ show n
    where
      var inner = inner >>* A.ActualVariable
--}}}
--{{{ intrinsic PROC call
intrinsicProcName :: OccParser (String, [A.Formal])
intrinsicProcName
    =  do n <- anyName A.ProcName
          let s = A.nameName n
          case lookup s intrinsicProcs of
            Just atns -> return (s, [A.Formal am t (A.Name emptyMeta A.VariableName n)
                                     | (am, t, n) <- atns])
            Nothing -> pzero

intrinsicProc :: OccParser A.Process
intrinsicProc
    =  do m <- md
          (s, fs) <- tryVX intrinsicProcName sLeftR
          as <- actuals fs
          sRightR
          eol
          return $ A.IntrinsicProcCall m s as
    <?> "intrinsic PROC instance"
--}}}
--}}}
--{{{ top-level forms

-- | An item at the top level is either a specification, or the end of the
-- file.
topLevelItem :: OccParser A.AST
topLevelItem
    =   handleSpecs (allocation <|> specification) topLevelItem
                    (\m s inner -> A.Spec m s inner)
    <|> do m <- md
           eof
           -- Stash the current locals so that we can either restore them
           -- when we get back to the file we included this one from, or
           -- pull the TLP name from them at the end.
           modify $ (\ps -> ps { csMainLocals = csLocalNames ps })
           return $ A.Several m []

-- | A source file is a series of nested specifications.
-- The later specifications must be in scope for the earlier ones.
-- We represent this as an 'AST' -- a @Structured ()@.
sourceFile :: OccParser (A.AST, [WarningReport], CompState)
sourceFile
    =   do p <- topLevelItem
           (w, s) <- getState
           return (p, w, s)
--}}}
--}}}

--{{{  entry points for the parser itself
-- | Parse a token stream with the given production.
runTockParser :: [Token] -> OccParser t -> CompState -> PassM t
runTockParser toks prod cs
    =  do case runParser prod ([], cs) "" toks of
            Left err ->
              -- If a position was encoded into the message, use that;
              -- else use the parser position.
              let errMeta = sourcePosToMeta $ errorPos err
                  (msgMeta, msg) = unpackMeta $ show err
                  m = Just errMeta >> msgMeta
                in dieReport (m, "Parse error: " ++ msg)
            Right r -> return r

-- | Parse an occam program.
parseOccamProgram :: [Token] -> PassM A.AST
parseOccamProgram toks
    =  do cs <- get
          (p, ws, cs') <- runTockParser toks sourceFile cs
          put cs'
          mapM_ warnReport ws
          return p
--}}}

