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

import Control.Monad (liftM, when)
import Control.Monad.State (MonadState, modify, get, put)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Text.ParserCombinators.Parsec

import qualified AST as A
import CompState
import Errors
import EvalConstants
import EvalLiterals
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
sAmp, sAssign, sBang, sColon, sColons, sComma, sEq, sLeft, sLeftR, sQuest,
  sRight, sRightR, sSemi
    :: OccParser ()

sAmp = reserved "&"
sAssign = reserved ":="
sBang = reserved "!"
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
  sINLINE, sIN, sINT, sINT16, sINT32, sINT64, sIS, sMINUS, sMOSTNEG, sMOSTPOS,
  sNOT, sOF, sOFFSETOF, sOR, sPACKED, sPAR, sPLACE, sPLACED, sPLUS, sPORT,
  sPRI, sPROC, sPROCESSOR, sPROTOCOL, sREAL32, sREAL64, sRECORD, sREM,
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

tryVVXV :: OccParser a -> OccParser b -> OccParser c -> OccParser d -> OccParser (a, b, d)
tryVVXV a b c d = try (do { av <- a; bv <- b; c; dv <- d; return (av, bv, dv) })

tryVXVXX :: OccParser a -> OccParser b -> OccParser c -> OccParser d -> OccParser e -> OccParser (a, c)
tryVXVXX a b c d e = try (do { av <- a; b; cv <- c; d; e; return (av, cv) })
--}}}

--{{{ subscripts
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
          t' <- subscriptType sub t
          rest <- postSubscripts t'
          return $ sub : rest)
      <|> return []

postSubscript :: A.Type -> OccParser A.Subscript
postSubscript t
    =  do m <- md
          t' <- resolveUserType m t
          case t' of
            A.Record _ ->
              do f <- tryXV sLeft fieldName
                 sRight
                 return $ A.SubscriptField m f
            A.Array _ _ ->
              do e <- tryXV sLeft intExpr
                 sRight
                 return $ A.Subscript m A.CheckBoth e
            _ -> pzero

maybeSliced :: OccParser a -> (Meta -> A.Subscript -> a -> a) -> (a -> OccParser A.Type) -> OccParser a
maybeSliced inner subscripter typer
    =  do m <- md

          (v, ff1) <- tryXVV sLeft inner fromOrFor
          t <- typer v >>= underlyingType m
          case t of
            (A.Array _ _) -> return ()
            _ -> dieP m $ "slice of non-array type " ++ showOccam t

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

-- | Find the type of a table literal given the types of its components.
-- This'll always return an Array; the inner type will either be the type of
-- the elements if they're all the same (in which case it's either an array
-- literal, or a record where all the fields are the same type), or Any if
-- they're not (i.e. if it's a record literal or an empty array).
tableType :: Meta -> [A.Type] -> OccParser A.Type
tableType m l = tableType' m (length l) l
  where
    tableType' m len [t] = return $ addDimensions [A.Dimension len] t
    tableType' m len (t1 : rest@(t2 : _))
        = if t1 == t2 then tableType' m len rest
                      else return $ addDimensions [A.Dimension len] A.Any
    tableType' m len [] = return $ addDimensions [A.Dimension 0] A.Any

-- | Check that the second dimension can be used in a context where the first
-- is expected.
isValidDimension :: A.Dimension -> A.Dimension -> Bool
isValidDimension A.UnknownDimension A.UnknownDimension = True
isValidDimension A.UnknownDimension (A.Dimension _) = True
isValidDimension (A.Dimension n1) (A.Dimension n2) = n1 == n2
isValidDimension _ _ = False

-- | Check that the second second of dimensions can be used in a context where
-- the first is expected.
areValidDimensions :: [A.Dimension] -> [A.Dimension] -> Bool
areValidDimensions [] [] = True
areValidDimensions (d1:ds1) (d2:ds2)
    = if isValidDimension d1 d2
        then areValidDimensions ds1 ds2
        else False
areValidDimensions _ _ = False

-- | Check that a type we've inferred matches the type we expected.
matchType :: Meta -> A.Type -> A.Type -> OccParser ()
matchType m et rt
    = case (et, rt) of
        ((A.Array ds t), (A.Array ds' t')) ->
          if areValidDimensions ds ds'
            then matchType m t t'
            else bad
        _ -> if rt == et then return () else bad
  where
    bad :: OccParser ()
    bad = dieP m $ "type mismatch (got " ++ showOccam rt ++ "; expected " ++ showOccam et ++ ")"

-- | Check that two lists of types match (for example, for parallel assignment).
matchTypes :: Meta -> [A.Type] -> [A.Type] -> OccParser ()
matchTypes m ets rts
    = sequence_ [matchType m et rt | (et, rt) <- zip ets rts]

-- | Parse a production inside a particular type context.
inTypeContext :: Maybe A.Type -> OccParser a -> OccParser a
inTypeContext ctx body
    =  do pushTypeContext ctx
          v <- body
          popTypeContext
          return v

-- | Parse a production with no particular type context (i.e. where we're
-- inside some bit of an expression that means we can't tell what the type is).
noTypeContext :: OccParser a -> OccParser a
noTypeContext = inTypeContext Nothing
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

makeUniqueName :: String -> OccParser String
makeUniqueName s
    =  do st <- get
          put $ st { csNameCounter = csNameCounter st + 1 }
          return $ s ++ "_u" ++ show (csNameCounter st)

findUnscopedName :: A.Name -> OccParser A.Name
findUnscopedName n@(A.Name m nt s)
    =  do st <- get
          case Map.lookup s (csUnscopedNames st) of
            Just s' -> return $ A.Name m nt s'
            Nothing ->
              do s' <- makeUniqueName s
                 modify (\st -> st { csUnscopedNames = Map.insert s s' (csUnscopedNames st) })
                 return $ A.Name m nt s'

scopeIn :: A.Name -> A.SpecType -> A.AbbrevMode -> OccParser A.Name
scopeIn n@(A.Name m nt s) t am
    =  do st <- getState
          s' <- makeUniqueName s
          let n' = n { A.nameName = s' }
          let nd = A.NameDef {
            A.ndMeta = m,
            A.ndName = s',
            A.ndOrigName = s,
            A.ndNameType = A.nameType n',
            A.ndType = t,
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
    =  do (s, t) <- tryXVXV sLeft constIntExpr sRight element
          sVal <- evalIntExpression s
          return $ addDimensions [A.Dimension sVal] t

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
    =   do { sTIMER; return $ A.Timer }
    <|> arrayType timerType
    <?> "timer type"

portType :: OccParser A.Type
portType
    =   do { sPORT; sOF; p <- dataType; return $ A.Port p }
    <|> arrayType portType
    <?> "port type"
--}}}
--{{{ literals
--{{{ type utilities for literals
-- | Can a literal of type rawT be used as a value of type wantT?
isValidLiteralType :: Meta -> A.Type -> A.Type -> OccParser Bool
isValidLiteralType m rawT wantT
    =  do underT <- resolveUserType m wantT
          case (rawT, underT) of
            -- We don't yet know what type we want -- so assume it's OK for now.
            (_, A.Any) -> return True
            (A.Real32, _) -> return $ isRealType underT
            (A.Int, _) -> return $ isIntegerType underT
            (A.Byte, _) -> return $ isIntegerType underT
            (A.Array (A.Dimension nf:_) _, A.Record _) ->
              -- We can't be sure without looking at the literal itself,
              -- so we need to do that below.
              do fs <- recordFields m wantT
                 return $ nf == length fs
            (A.Array (d1:ds1) t1, A.Array (d2:ds2) t2) ->
              -- Check the outermost dimension is OK, then recurse.
              -- We can't just look at all the dimensions because this
              -- might be an array of a record type, or similar.
              if isValidDimension d2 d1
                then do rawT' <- trivialSubscriptType m rawT
                        underT' <- trivialSubscriptType m underT
                        isValidLiteralType m rawT' underT'
                else return False
            _ -> return $ rawT == wantT

-- | Apply dimensions from one type to another as far as possible.
-- This should only be used when you know the two types are compatible first
-- (i.e. they've passed isValidLiteralType).
applyDimensions :: A.Type -> A.Type -> A.Type
applyDimensions (A.Array ods _) (A.Array tds t) = A.Array (dims ods tds) t
  where
    dims :: [A.Dimension] -> [A.Dimension] -> [A.Dimension]
    dims (d@(A.Dimension _):ods) (A.UnknownDimension:tds)
        = d : dims ods tds
    dims (_:ods) (d:tds)
        = d : dims ods tds
    dims _ ds = ds
applyDimensions _ t = t

-- | Convert a raw array element literal into its real form.
makeArrayElem :: A.Type -> A.ArrayElem -> OccParser A.ArrayElem
makeArrayElem t@(A.Array _ _) (A.ArrayElemArray aes)
    =  do elemT <- trivialSubscriptType (findMeta aes) t
          liftM A.ArrayElemArray $ mapM (makeArrayElem elemT) aes
makeArrayElem _ (A.ArrayElemArray es)
    = dieP (findMeta es) $ "unexpected nested array literal"
-- A nested array literal that's still of array type (i.e. it's not a
-- record inside the array) -- collapse it.
makeArrayElem t@(A.Array _ _) (A.ArrayElemExpr (A.Literal _ _ (A.ArrayLiteral m aes)))
    =  do elemT <- trivialSubscriptType m t
          liftM A.ArrayElemArray $ mapM (makeArrayElem elemT) aes
makeArrayElem t (A.ArrayElemExpr e)
    = liftM A.ArrayElemExpr $ makeLiteral e t

-- | Given a raw literal and the type that it should be, either produce a
-- literal of that type, or fail with an appropriate error if it's not a valid
-- value of that type.
makeLiteral :: A.Expression -> A.Type -> OccParser A.Expression
-- A literal.
makeLiteral x@(A.Literal m t lr) wantT
    =  do underT <- resolveUserType m wantT

          typesOK <- isValidLiteralType m t wantT
          when (not typesOK) $
            dieP m $ "default type of literal (" ++ showOccam t ++ ") cannot be coerced to desired type (" ++ showOccam wantT ++ ")"

          case (underT, lr) of
            -- An array literal.
            (A.Array _ _, A.ArrayLiteral ml aes) ->
              do elemT <- trivialSubscriptType ml underT
                 aes' <- mapM (makeArrayElem elemT) aes
                 return $ A.Literal m (applyDimensions t wantT) (A.ArrayLiteral ml aes')
            -- A record literal -- which we need to convert from the raw
            -- representation.
            (A.Record _, A.ArrayLiteral ml aes)  ->
              do fs <- recordFields m underT
                 es <- sequence [case ae of
                                   A.ArrayElemExpr e -> makeLiteral e t
                                   A.ArrayElemArray aes ->
                                     makeLiteral (A.Literal m t $ A.ArrayLiteral ml aes) t
                                 | ((_, t), ae) <- zip fs aes]
                 return $ A.Literal m wantT (A.RecordLiteral ml es)
            -- Some other kind of literal (one of the trivial types).
            _ -> return $ A.Literal m wantT lr
-- A subscript; figure out what the type of the thing being subscripted must be
-- and recurse.
makeLiteral (A.SubscriptedExpr m sub e) wantT
    =  do inWantT <- unsubscriptType sub wantT
          e' <- makeLiteral e inWantT
          return $ A.SubscriptedExpr m sub e'
-- Something that's not a literal (which we've found inside a table) -- just
-- check it's the right type.
makeLiteral e wantT
    =  do t <- typeOfExpression e
          matchType (findMeta e) wantT t
          return e
--}}}

typeDecorator :: OccParser (Maybe A.Type)
typeDecorator
    =   do sLeftR
           t <- dataType
           sRightR
           return $ Just t
    <|> return Nothing
    <?> "literal type decorator"

literal :: OccParser A.Expression
literal
    =  do m <- md
          (lr, t) <- untypedLiteral
          dec <- typeDecorator
          ctx <- getTypeContext
          let lit = A.Literal m t lr
          case (dec, ctx) of
            (Just wantT, _) -> makeLiteral lit wantT
            (_, Just wantT) -> makeLiteral lit wantT
            _ -> return lit
    <?> "literal"

untypedLiteral :: OccParser (A.LiteralRepr, A.Type)
untypedLiteral
    =   do { r <- real; return (r, A.Real32) }
    <|> do { r <- integer; return (r, A.Int) }
    <|> do { r <- byte; return (r, A.Byte) }

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
    =   do e <- maybeSubscripted "table" table' A.SubscriptedExpr typeOfExpression
           rawT <- typeOfExpression e
           ctx <- getTypeContext
           case ctx of
             Just wantT -> makeLiteral e wantT
             _ -> return e

table' :: OccParser A.Expression
table'
    =   do m <- md
           (lr, t) <- tableElems
           dec <- typeDecorator
           let lit = A.Literal m t lr
           case dec of
             Just wantT -> makeLiteral lit wantT
             _ -> return lit
    <|> maybeSliced table A.SubscriptedExpr typeOfExpression
    <?> "table'"

tableElems :: OccParser (A.LiteralRepr, A.Type)
tableElems
    =   do (lr, dim) <- stringLiteral
           return (lr, A.Array [dim] A.Byte)
    <|> do m <- md
           es <- tryXVX sLeft (noTypeContext $ sepBy1 expression sComma) sRight
           -- Constant fold early, so that tables have a better chance of
           -- becoming constants.
           (es', _, _) <- liftM unzip3 $ sequence [constantFold e | e <- es]
           ets <- mapM typeOfExpression es'
           defT <- tableType m ets
           return (A.ArrayLiteral m (map A.ArrayElemExpr es'), defT)
    <?> "table elements"

stringLiteral :: OccParser (A.LiteralRepr, A.Dimension)
stringLiteral
    =  do m <- md
          cs <- stringCont <|> stringLit
          let aes = [A.ArrayElemExpr $ A.Literal m' A.Byte c
                     | c@(A.ByteLiteral m' _) <- cs]
          return (A.ArrayLiteral m aes, A.Dimension $ length cs)
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
expressionList :: [A.Type] -> OccParser A.ExpressionList
expressionList types
    =   functionMulti types
    <|> do m <- md
           es <- intersperseP (map expressionOfType types) sComma
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
           t <- typeOfExpression l
           r <- operandOfType t
           return $ A.Dyadic m o l r
    <|> do m <- md
           (l, o) <- tryVV operand shiftOperator
           r <- operandOfType A.Int
           return $ A.Dyadic m o l r
    <|> do m <- md
           (l, o) <- tryVV (noTypeContext operand) comparisonOperator
           t <- typeOfExpression l
           r <- operandOfType t
           return $ A.Dyadic m o l r
    <|> do m <- md
           (l, o) <- tryVV operand dyadicOperator
           t <- typeOfExpression l
           r <- operandOfType t
           return $ A.Dyadic m o l r
    <|> associativeOpExpression
    <|> conversion
    <|> operand
    <?> "expression"

associativeOpExpression :: OccParser A.Expression
associativeOpExpression
    =  do m <- md
          (l, o) <- tryVV operand associativeOperator
          tl <- typeOfExpression l
          r <- associativeOpExpression <|> operand
          tr <- typeOfExpression r
          matchType m tl tr
          return $ A.Dyadic m o l r
    <?> "associative operator expression"

sizeExpr :: OccParser A.Expression
sizeExpr
    =  do m <- md
          sSIZE
          do { t <- dataType; return $ A.SizeType m t }
            <|> do v <- noTypeContext operand
                   return $ A.SizeExpr m v
            <|> do v <- noTypeContext (channel <|> timer <|> port)
                   return $ A.SizeVariable m v
    <?> "SIZE expression"

--{{{ type-constrained expressions
expressionOfType :: A.Type -> OccParser A.Expression
expressionOfType wantT
    =  do e <- inTypeContext (Just wantT) expression
          t <- typeOfExpression e
          matchType (findMeta e) wantT t
          return e

intExpr :: OccParser A.Expression
intExpr = expressionOfType A.Int <?> "integer expression"
booleanExpr :: OccParser A.Expression
booleanExpr = expressionOfType A.Bool <?> "boolean expression"

constExprOfType :: A.Type -> OccParser A.Expression
constExprOfType wantT
    =  do e <- expressionOfType wantT
          (e', isConst, (m,msg)) <- constantFold e
          when (not isConst) $
            dieReport (m,"expression is not constant (" ++ msg ++ ")")
          return e'

constIntExpr :: OccParser A.Expression
constIntExpr = constExprOfType A.Int <?> "constant integer expression"

operandOfType :: A.Type -> OccParser A.Expression
operandOfType wantT
    =  do o <- inTypeContext (Just wantT) operand
          t <- typeOfExpression o
          matchType (findMeta o) wantT t
          return o
--}}}
--{{{ functions
functionNameValued :: Bool -> OccParser A.Name
functionNameValued isMulti
    =  do n <- functionName
          rts <- returnTypesOfFunction n
          case (rts, isMulti) of
            ([_], False) -> return n
            ((_:_:_), True) -> return n
            _ -> pzero
    <?> "function name"

functionActuals :: [A.Formal] -> OccParser [A.Expression]
functionActuals fs
    =  do let actuals = [expressionOfType t <?> "actual for " ++ show n
                         | A.Formal _ t n <- fs]
          es <- intersperseP actuals sComma
          return es

functionSingle :: OccParser A.Expression
functionSingle
    =  do m <- md
          n <- tryVX (functionNameValued False) sLeftR
          A.Function _ _ _ fs _ <- specTypeOfName n
          as <- functionActuals fs
          sRightR
          return $ A.FunctionCall m n as
    <?> "single-valued function call"

functionMulti :: [A.Type] -> OccParser A.ExpressionList
functionMulti types
    =  do m <- md
          n <- tryVX (functionNameValued True) sLeftR
          A.Function _ _ _ fs _ <- specTypeOfName n
          as <- functionActuals fs
          sRightR
          rts <- returnTypesOfFunction n
          matchTypes m types rts
          return $ A.FunctionCallList m n as
    <?> "multi-valued function call"
--}}}
--{{{ intrinsic functions
intrinsicFunctionName :: Bool -> OccParser (String, [A.Type], [A.Formal])
intrinsicFunctionName isMulti
    =  do n <- anyName A.FunctionName
          let s = A.nameName n
          case (lookup s intrinsicFunctions, isMulti) of
            (Nothing, _) -> pzero
            (Just ([_], _), True) -> pzero
            (Just ((_:_:_), _), False) -> pzero
            (Just (rts, tns), _) ->
              return (s, rts, [A.Formal A.ValAbbrev t (A.Name emptyMeta A.VariableName n)
                               | (t, n) <- tns])
    <?> "intrinsic function name"

intrinsicFunctionSingle :: OccParser A.Expression
intrinsicFunctionSingle
    =  do m <- md
          (s, _, fs) <- tryVX (intrinsicFunctionName False) sLeftR
          as <- functionActuals fs
          sRightR
          return $ A.IntrinsicFunctionCall m s as
    <?> "single-valued intrinsic function call"

-- No support for multi-valued intrinsic functions, because I don't think there
-- are likely to be any, and supporting them in the C backend is slightly
-- tricky.
--}}}

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
    <?> "dyadic operator"

-- These always need an INT on their right-hand side.
shiftOperator :: OccParser A.DyadicOp
shiftOperator
    =   do { reserved "<<"; return A.LeftShift }
    <|> do { reserved ">>"; return A.RightShift }
    <?> "shift operator"

-- These always return a BOOL, so we have to deal with them specially for type
-- context.
comparisonOperator :: OccParser A.DyadicOp
comparisonOperator
    =   do { reserved "="; return A.Eq }
    <|> do { reserved "<>"; return A.NotEq }
    <|> do { reserved "<"; return A.Less }
    <|> do { reserved ">"; return A.More }
    <|> do { reserved "<="; return A.LessEq }
    <|> do { reserved ">="; return A.MoreEq }
    <|> do { sAFTER; return A.After }
    <?> "comparison operator"

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
          baseT <- underlyingType m t
          (c, o) <- conversionMode
          ot <- typeOfExpression o
          baseOT <- underlyingType m ot
          c <- case (isPreciseConversion baseOT baseT, c) of
                 (False, A.DefaultConversion) ->
                   dieP m "imprecise conversion must specify ROUND or TRUNC"
                 (False, _) -> return c
                 (True, A.DefaultConversion) -> return c
                 (True, _) ->
                   do addWarning m "precise conversion specifies ROUND or TRUNC; ignored"
                      return A.DefaultConversion
          return $ A.Conversion m c t o
    <?> "conversion"

conversionMode :: OccParser (A.ConversionMode, A.Expression)
conversionMode
    =   do { sROUND; o <- noTypeContext operand; return (A.Round, o) }
    <|> do { sTRUNC; o <- noTypeContext operand; return (A.Trunc, o) }
    <|> do { o <- noTypeContext operand; return (A.DefaultConversion, o) }
    <?> "conversion mode and operand"
--}}}
--{{{ operands
operand :: OccParser A.Expression
operand
    = maybeSubscripted "operand" operand' A.SubscriptedExpr typeOfExpression

operand' :: OccParser A.Expression
operand'
    =   do { m <- md; v <- variable; return $ A.ExprVariable m v }
    <|> literal
    <|> do { sLeftR; e <- expression; sRightR; return e }
-- XXX value process
    <|> functionSingle
    <|> intrinsicFunctionSingle
    <|> do m <- md
           sBYTESIN
           sLeftR
           (try (do { o <- noTypeContext operand; sRightR; return $ A.BytesInExpr m o }))
             <|> do { t <- dataType; sRightR; return $ A.BytesInType m t }
    <|> do { m <- md; sOFFSETOF; sLeftR; t <- dataType; sComma; f <- fieldName; sRightR; return $ A.OffsetOf m t f }
    <|> do { m <- md; sTRUE; return $ A.True m }
    <|> do { m <- md; sFALSE; return $ A.False m }
    <|> table
    <?> "operand"
--}}}
--{{{ variables, channels, timers, ports
variable :: OccParser A.Variable
variable
    = maybeSubscripted "variable" variable' A.SubscriptedVariable typeOfVariable

variable' :: OccParser A.Variable
variable'
    =   do { m <- md; n <- try variableName; return $ A.Variable m n }
    <|> maybeSliced variable A.SubscriptedVariable typeOfVariable
    <?> "variable'"

variableOfType :: A.Type -> OccParser A.Variable
variableOfType wantT
    =  do v <- variable
          t <- typeOfVariable v
          matchType (findMeta v) wantT t
          return v

channel :: OccParser A.Variable
channel
    =   maybeSubscripted "channel" channel' A.SubscriptedVariable typeOfVariable
    <?> "channel"

channel' :: OccParser A.Variable
channel'
    =   do { m <- md; n <- try channelName; return $ A.Variable m n }
    <|> maybeSliced channel A.SubscriptedVariable typeOfVariable
    <?> "channel'"

channelOfType :: A.Type -> OccParser A.Variable
channelOfType wantT
    =  do c <- channel
          t <- typeOfVariable c
          matchType (findMeta c) wantT t
          return c

timer :: OccParser A.Variable
timer
    =   maybeSubscripted "timer" timer' A.SubscriptedVariable typeOfVariable
    <?> "timer"

timer' :: OccParser A.Variable
timer'
    =   do { m <- md; n <- try timerName; return $ A.Variable m n }
    <|> maybeSliced timer A.SubscriptedVariable typeOfVariable
    <?> "timer'"

port :: OccParser A.Variable
port
    =   maybeSubscripted "port" port' A.SubscriptedVariable typeOfVariable
    <?> "port"

port' :: OccParser A.Variable
port'
    =   do { m <- md; n <- try portName; return $ A.Variable m n }
    <|> maybeSliced port A.SubscriptedVariable typeOfVariable
    <?> "port'"

portOfType :: A.Type -> OccParser A.Variable
portOfType wantT
    =  do p <- port
          t <- typeOfVariable p
          matchType (findMeta p) wantT t
          return p
--}}}
--{{{ protocols
protocol :: OccParser A.Type
protocol
    =   do { n <- try protocolName ; return $ A.UserProtocol n }
    <|> simpleProtocol
    <?> "protocol"

simpleProtocol :: OccParser A.Type
simpleProtocol
    =   do { l <- tryVX dataType sColons; sLeft; sRight; r <- dataType; return $ A.Counted l r }
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
          b <- intExpr
          sFOR
          c <- intExpr
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
    =   do sAT
           e <- intExpr
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
    <|> isAbbrev newVariableName variable
    <|> isAbbrev newChannelName channel
    <|> chanArrayAbbrev
    <|> isAbbrev newTimerName timer
    <|> isAbbrev newPortName port
    <?> "abbreviation"

valIsAbbrev :: OccParser A.Specification
valIsAbbrev
    =  do m <- md
          (n, t, e) <- do { n <- tryXVX sVAL newVariableName sIS; e <- expression; sColon; eol; t <- typeOfExpression e; return (n, t, e) }
                       <|> do { (s, n) <- tryXVVX sVAL dataSpecifier newVariableName sIS; e <- expressionOfType s; sColon; eol; return (n, s, e) }
          -- Do constant folding early, so that we can use names defined this
          -- way as constants elsewhere.
          (e', _, _) <- constantFold e
          return $ A.Specification m n $ A.IsExpr m A.ValAbbrev t e'
    <?> "VAL IS abbreviation"

isAbbrev :: OccParser A.Name -> OccParser A.Variable -> OccParser A.Specification
isAbbrev newName oldVar
    =   do m <- md
           (n, v) <- tryVXV newName sIS oldVar
           sColon
           eol
           t <- typeOfVariable v
           return $ A.Specification m n $ A.Is m A.Abbrev t v
    <|> do m <- md
           (s, n, v) <- tryVVXV specifier newName sIS oldVar
           sColon
           eol
           t <- typeOfVariable v
           matchType m s t
           return $ A.Specification m n $ A.Is m A.Abbrev s v
    <?> "IS abbreviation"

chanArrayAbbrev :: OccParser A.Specification
chanArrayAbbrev
    =   do m <- md
           (n, cs) <- tryVXXV newChannelName sIS sLeft (sepBy1 channel sComma)
           sRight
           sColon
           eol
           ts <- mapM typeOfVariable cs
           t <- tableType m ts
           case t of
             (A.Array _ (A.Chan {})) -> return ()
             _ -> dieP m $ "types do not match in channel array abbreviation"
           return $ A.Specification m n $ A.IsChannelArray m t cs
    <|> do m <- md
           (ct, s, n) <- try (do s <- channelSpecifier
                                 n <- newChannelName
                                 sIS
                                 sLeft
                                 ct <- trivialSubscriptType m s
                                 case ct of
                                   A.Chan {} -> return (ct, s, n)
                                   _ -> pzero)
           cs <- sepBy1 (channelOfType ct) sComma
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
           do { sIS; fs' <- scopeInFormals fs; el <- expressionList rs; scopeOutFormals fs'; sColon; eol; return $ A.Specification m n $ A.Function m sm rs fs' (Left $ A.Only m el) }
             <|> do { eol; indent; fs' <- scopeInFormals fs; vp <- valueProcess rs; scopeOutFormals fs'; outdent; sColon; eol; return $ A.Specification m n $ A.Function m sm rs fs' (Left vp) }
    <|> retypesAbbrev
    <?> "definition"

retypesReshapes :: OccParser ()
retypesReshapes
    = sRETYPES <|> sRESHAPES

retypesAbbrev :: OccParser A.Specification
retypesAbbrev
    =   do m <- md
           (s, n) <- tryVVX dataSpecifier newVariableName retypesReshapes
           v <- variable
           sColon
           eol
           origT <- typeOfVariable v
           checkRetypes m origT s
           return $ A.Specification m n $ A.Retypes m A.Abbrev s v
    <|> do m <- md
           (s, n) <- tryVVX channelSpecifier newChannelName retypesReshapes
           c <- channel
           sColon
           eol
           origT <- typeOfVariable c
           checkRetypes m origT s
           return $ A.Specification m n $ A.Retypes m A.Abbrev s c
    <|> do m <- md
           (s, n) <- tryXVVX sVAL dataSpecifier newVariableName retypesReshapes
           e <- expression
           sColon
           eol
           origT <- typeOfExpression e
           checkRetypes m origT s
           return $ A.Specification m n $ A.RetypesExpr m A.ValAbbrev s e
    <?> "RETYPES/RESHAPES abbreviation"

-- | Check that a RETYPES\/RESHAPES is safe.
checkRetypes :: Meta -> A.Type -> A.Type -> OccParser ()
-- Retyping channels is always "safe".
checkRetypes _ (A.Chan {}) (A.Chan {}) = return ()
checkRetypes m fromT toT
    =  do bf <- bytesInType fromT
          bt <- bytesInType toT
          case (bf, bt) of
            (BIJust a, BIJust b) ->
              when (a /= b) $ dieP m "size mismatch in RETYPES"
            (BIJust a, BIOneFree b _) ->
              when (not ((b <= a) && (a `mod` b == 0))) $ dieP m "size mismatch in RETYPES"
            (_, BIManyFree) ->
              dieP m "multiple free dimensions in RETYPES/RESHAPES type"
            -- Otherwise we have to do a runtime check.
            _ -> return ()

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

valueProcess :: [A.Type] -> OccParser (A.Structured A.ExpressionList)
valueProcess rs
    =   do m <- md
           sVALOF
           eol
           indent
           p <- process
           sRESULT
           el <- expressionList rs
           eol
           outdent
           return $ A.ProcThen m p (A.Only m el)
    <|> handleSpecs specification (valueProcess rs) A.Spec
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
           -- We ignore dimensions here because we do the check at runtime.
           ts <- sequence [liftM removeFixedDimensions $ typeOfVariable v | v <- vs]
           es <- expressionList ts
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
           A.Port t <- typeOfVariable p
           v <- variableOfType t
           eol
           return (p, A.InputSimple m [A.InVariable m v])
    <?> "input"

channelInput :: OccParser (A.Variable, A.InputMode)
channelInput
    =   do m <- md
           c <- tryVX channel sQuest
           pis <- protocolItems c
           case pis of
             Left ts ->
               do is <- intersperseP (map inputItem ts) sSemi
                  eol
                  return (c, A.InputSimple m is)
             Right nts ->
               do sCASE
                  tl <- taggedList nts
                  eol
                  return (c, A.InputCase m (A.Only m (tl (A.Skip m))))
    <?> "channel input"

timerInput :: OccParser (A.Variable, A.InputMode)
timerInput
    =   do m <- md
           c <- tryVX timer sQuest
           do { v <- variableOfType A.Int; eol; return (c, A.InputTimerRead m (A.InVariable m v)) }
             <|> do { sAFTER; e <- intExpr; eol; return (c, A.InputTimerAfter m e) }
    <?> "timer input"

taggedList :: [(A.Name, [A.Type])] -> OccParser (A.Process -> A.Variant)
taggedList nts
    =  do m <- md
          tag <- tagName
          ts <- checkJust (Just m, "unknown tag in protocol") $ lookup tag nts
          is <- sequence [sSemi >> inputItem t | t <- ts]
          return $ A.Variant m tag is
    <?> "tagged list"

inputItem :: A.Type -> OccParser A.InputItem
inputItem t
    = case t of
        (A.Counted ct it) ->
          do m <- md
             v <- variableOfType ct
             sColons
             w <- variableOfType (addDimensions [A.UnknownDimension] it)
             return $ A.InCounted m v w
        A.Any ->
          do m <- md
             v <- variable
             return $ A.InVariable m v
        _ ->
          do m <- md
             v <- variableOfType t
             return $ A.InVariable m v
    <?> "input item"
--}}}
--{{{ variant input (? CASE)
caseInputItems :: A.Variable -> OccParser [(A.Name, [A.Type])]
caseInputItems c
    =   do pis <- protocolItems c
           case pis of
             Left _ -> dieP (findMeta c) "CASE input on channel of non-variant protocol"
             Right nts -> return nts

caseInput :: OccParser A.Process
caseInput
    =   do m <- md
           c <- tryVX channel (do {sQuest; sCASE; eol})
           nts <- caseInputItems c
           vs <- maybeIndentedList m "empty ? CASE" (variant nts)
           return $ A.Input m c (A.InputCase m (A.Several m vs))
    <?> "case input"

variant :: [(A.Name, [A.Type])] -> OccParser (A.Structured A.Variant)
variant nts
    =   do m <- md
           tl <- taggedList nts
           eol
           indent
           p <- process
           outdent
           return $ A.Only m (tl p)
    <|> handleSpecs specification (variant nts) A.Spec
    <?> "variant"
--}}}
--{{{ output (!)
output :: OccParser A.Process
output
    =   channelOutput
    <|> do m <- md
           p <- tryVX port sBang
           A.Port t <- typeOfVariable p
           e <- expressionOfType t
           eol
           return $ A.Output m p [A.OutExpression m e]
    <?> "output"

channelOutput :: OccParser A.Process
channelOutput
    =   do m <- md
           c <- tryVX channel sBang
           -- This is an ambiguity in the occam grammar; you can't tell in "a ! b"
           -- whether b is a variable or a tag, without knowing the type of a.
           pis <- protocolItems c
           case pis of
             Left ts ->
               do os <- intersperseP (map outputItem ts) sSemi
                  eol
                  return $ A.Output m c os
             Right nts ->
               do tag <- tagName
                  ts <- checkJust (Just m, "unknown tag in protocol") $ lookup tag nts
                  os <- sequence [sSemi >> outputItem t | t <- ts]
                  eol
                  return $ A.OutputCase m c tag os
    <?> "channel output"

outputItem :: A.Type -> OccParser A.OutputItem
outputItem t
    = case t of
        (A.Counted ct it) ->
          do m <- md
             a <- expressionOfType ct
             sColons
             b <- expressionOfType (addDimensions [A.UnknownDimension] it)
             return $ A.OutCounted m a b
        A.Any ->
          do m <- md
             e <- expression
             t <- typeOfExpression e
             return $ A.OutExpression m e
        _ ->
          do m <- md
             e <- expressionOfType t
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
           b <- booleanExpr
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
           t <- typeOfExpression sel
           t' <- underlyingType m t
           when (not $ isCaseableType t') $ dieP m "case selector has non-CASEable type"
           eol
           os <- maybeIndentedList m "empty CASE" (caseOption t)
           return $ A.Case m sel (A.Several m os)
    <?> "CASE process"

caseOption :: A.Type -> OccParser (A.Structured A.Option)
caseOption t
    =   do m <- md
           ces <- tryVX (sepBy (constExprOfType t) sComma) eol
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
    <|> handleSpecs specification (caseOption t) A.Spec
    <?> "option"
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
           e <- intExpr
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
           (b, c) <- tryVXVXX booleanExpr sAmp channel sQuest (sCASE >> eol)
           nts <- caseInputItems c
           vs <- maybeIndentedList m "empty ? CASE" (variant nts)
           return $ A.Only m (A.AlternativeCond m b c (A.InputCase m $ A.Several m vs) (A.Skip m))
    <|> do m <- md
           c <- tryVXX channel sQuest (sCASE >> eol)
           nts <- caseInputItems c
           vs <- maybeIndentedList m "empty ? CASE" (variant nts)
           return $ A.Only m (A.Alternative m c (A.InputCase m $ A.Several m vs) (A.Skip m))
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
           return $ A.Alternative m c im
    <|> do m <- md
           b <- tryVX booleanExpr sAmp
           do { (c, im) <- input; return $ A.AlternativeCond m b c im }
             <|> do { sSKIP; eol; return $ A.AlternativeSkip m b }
    <?> "guard"
--}}}
--{{{ PROC calls
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
            A.ValAbbrev ->
              do e <- expressionOfType t
                 return $ A.ActualExpression t e
            _ ->
              case stripArrayType t of
                A.Chan {} -> var (channelOfType t)
                A.Timer -> var timer
                A.Port _ -> var (portOfType t)
                _ -> var (variableOfType t)
    <?> "actual of type " ++ showOccam t ++ " for " ++ show n
    where
      var inner = liftM (A.ActualVariable am t) inner
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

