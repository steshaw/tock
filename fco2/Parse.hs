-- | Parse occam code into an AST.
module Parse where

import Control.Monad (liftM, when)
import Control.Monad.Error (runErrorT)
import Control.Monad.State (MonadState, StateT, execStateT, liftIO, modify, get, put)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace
import qualified IO
import Numeric (readHex)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language (emptyDef)
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.Regex

import qualified AST as A
import Errors
import EvalConstants
import EvalLiterals
import Indentation
import Intrinsics
import Metadata
import ParseState
import Pass
import Types
import Utils

--{{{ setup stuff for Parsec
type OccParser = GenParser Char ParseState

-- | Make MonadState functions work in the parser monad.
-- This came from <http://hackage.haskell.org/trac/ghc/ticket/1274> -- which means
-- it'll probably be in a future GHC release anyway.
instance MonadState st (GenParser tok st) where
  get = getState
  put = setState

instance Die (GenParser tok st) where
  die = fail

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
                          "<<",
                          ">>",
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
                          "IN",
                          "INLINE",
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
                          "WORKSPACE",
                          "VECSPACE",
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
md :: OccParser Meta
md
  =  do pos <- getPosition
        return Meta {
                 metaFile = Just $ sourceName pos,
                 metaLine = sourceLine pos,
                 metaColumn = sourceColumn pos
               }

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
          t' <- resolveUserType t
          case t' of
            A.Record _ ->
              do f <- tryXV sLeft fieldName
                 sRight
                 return $ A.SubscriptField m f
            A.Array _ _ ->
              do e <- tryXV sLeft intExpr
                 sRight
                 return $ A.Subscript m e
            _ -> pzero

maybeSliced :: OccParser a -> (Meta -> A.Subscript -> a -> a) -> (a -> OccParser A.Type) -> OccParser a
maybeSliced inner subscripter typer
    =  do m <- md

          (v, ff1) <- tryXVV sLeft inner fromOrFor
          t <- typer v >>= underlyingType
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

-- | Find the type of a table literal given the types of its components.
-- This'll always return an Array; the inner type will either be the type of
-- the elements if they're all the same (in which case it's either an array
-- literal, or a record where all the fields are the same type), or Any if
-- they're not (i.e. if it's a record literal or an empty array).
tableType :: Meta -> [A.Type] -> OccParser A.Type
tableType m l = tableType' m (length l) l
  where
    tableType' m len [t] = return $ makeArrayType (A.Dimension len) t
    tableType' m len (t1 : rest@(t2 : _))
        = if t1 == t2 then tableType' m len rest
                      else return $ makeArrayType (A.Dimension len) A.Any
    tableType' m len [] = return $ makeArrayType (A.Dimension 0) A.Any

-- | Check that the second second of dimensions can be used in a context where
-- the first is expected.
areValidDimensions :: [A.Dimension] -> [A.Dimension] -> Bool
areValidDimensions [] [] = True
areValidDimensions (A.UnknownDimension:ds1) (A.UnknownDimension:ds2)
    = areValidDimensions ds1 ds2
areValidDimensions (A.UnknownDimension:ds1) (A.Dimension _:ds2)
    = areValidDimensions ds1 ds2
areValidDimensions (A.Dimension n1:ds1) (A.Dimension n2:ds2)
    =  if n1 /= n2 then False else areValidDimensions ds1 ds2
areValidDimensions _ _ = False

-- | Check that a type we've inferred matches the type we expected.
matchType :: A.Type -> A.Type -> OccParser ()
matchType et rt
    = case (et, rt) of
        ((A.Array ds t), (A.Array ds' t')) ->
          if areValidDimensions ds ds'
            then matchType t t'
            else bad
        _ -> if rt == et then return () else bad
  where
    bad = fail $ "type mismatch (got " ++ show rt ++ "; expected " ++ show et ++ ")"

-- | Check that two lists of types match (for example, for parallel assignment).
matchTypes :: [A.Type] -> [A.Type] -> OccParser ()
matchTypes ets rts
    = sequence_ [matchType et rt | (et, rt) <- zip ets rts]

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
            A.ndAbbrevMode = am,
            A.ndPlacement = A.Unplaced
          }
          defineName n' nd
          modify $ (\st -> st {
                             psNameCounter = (psNameCounter st) + 1,
                             psLocalNames = (s, n') : (psLocalNames st)
                           })
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

channelName = name A.ChannelName
dataTypeName = name A.DataTypeName
functionName = name A.FunctionName
portName = name A.PortName
procName = name A.ProcName
protocolName = name A.ProtocolName
recordName = name A.RecordName
timerName = name A.TimerName
variableName = name A.VariableName

newChannelName = newName A.ChannelName
newDataTypeName = newName A.DataTypeName
newFunctionName = newName A.FunctionName
newPortName = newName A.PortName
newProcName = newName A.ProcName
newProtocolName = newName A.ProtocolName
newRecordName = newName A.RecordName
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
-- | A sized array of a production.
arrayType :: OccParser A.Type -> OccParser A.Type
arrayType element
    =  do (s, t) <- tryXVXV sLeft constIntExpr sRight element
          sVal <- evalIntExpression s
          return $ makeArrayType (A.Dimension sVal) t

-- | Either a sized or unsized array of a production.
specArrayType :: OccParser A.Type -> OccParser A.Type
specArrayType element
    =   arrayType element
    <|> do t <- tryXXV sLeft sRight element
           return $ makeArrayType A.UnknownDimension t

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

-- FIXME should probably make CHAN INT work, since that'd be trivial...
channelType :: OccParser A.Type
channelType
    =   do { sCHAN; sOF; p <- protocol; return $ A.Chan p }
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
    =  do case (rawT, wantT) of
            -- We don't yet know what type we want -- so assume it's OK for now.
            (_, A.Any) -> return True
            (A.Real32, _) -> return $ isRealType wantT
            (A.Int, _) -> return $ isIntegerType wantT
            (A.Byte, _) -> return $ isIntegerType wantT
            (A.Array (A.Dimension nf:_) _, A.Record _) ->
              -- We can't be sure without looking at the literal itself,
              -- so we need to do that below.
              do fs <- recordFields m wantT
                 return $ nf == length fs
            (A.Array ds1 t1, A.Array ds2 t2) ->
              if areValidDimensions ds2 ds1
                then isValidLiteralType m t1 t2
                else return False
            (a, b) -> return $ a == b

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
    =  do elemT <- trivialSubscriptType t
          liftM A.ArrayElemArray $ mapM (makeArrayElem elemT) aes
makeArrayElem _ (A.ArrayElemArray _)
    = fail $ "unexpected nested array literal"
-- A nested array literal that's still of array type (i.e. it's not a
-- record inside the array) -- collapse it.
makeArrayElem t@(A.Array _ _) (A.ArrayElemExpr (A.Literal _ _ (A.ArrayLiteral _ aes)))
    =  do elemT <- trivialSubscriptType t
          liftM A.ArrayElemArray $ mapM (makeArrayElem elemT) aes
makeArrayElem t (A.ArrayElemExpr e)
    = liftM A.ArrayElemExpr $ makeLiteral e t

-- | Given a raw literal and the type that it should be, either produce a
-- literal of that type, or fail with an appropriate error if it's not a valid
-- value of that type.
makeLiteral :: A.Expression -> A.Type -> OccParser A.Expression
-- A literal.
makeLiteral (A.Literal m t lr) wantT
    =  do underT <- underlyingType wantT

          typesOK <- isValidLiteralType m t underT
          when (not typesOK) $
            dieP m $ "default type of literal (" ++ show t ++ ") cannot be coerced to desired type (" ++ show wantT ++ ")"

          case (underT, lr) of
            -- An array literal.
            (A.Array _ _, A.ArrayLiteral ml aes) ->
              do elemT <- trivialSubscriptType underT
                 aes' <- mapM (makeArrayElem elemT) aes
                 return $ A.Literal m (applyDimensions t wantT) (A.ArrayLiteral ml aes')
            -- A record literal -- which we need to convert from the raw
            -- representation.
            (A.Record _, A.ArrayLiteral ml aes)  ->
              do fs <- recordFields m underT
                 es <- sequence [makeLiteral e t
                                 | ((_, t), A.ArrayElemExpr e) <- zip fs aes]
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
          matchType wantT t
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
           (l, r) <- tryVXVX digits (char '.') digits (char 'E')
           e <- lexeme occamExponent
           return $ A.RealLiteral m (l ++ "." ++ r ++ "E" ++ e)
    <|> do m <- md
           l <- tryVX digits (char '.')
           r <- lexeme digits
           return $ A.RealLiteral m (l ++ "." ++ r)
    <?> "real literal"

occamExponent :: OccParser String
occamExponent
    =  do c <- oneOf "+-"
          d <- digits
          return $ c : d
    <?> "exponent"

integer :: OccParser A.LiteralRepr
integer
    =  do m <- md
          do { d <- lexeme digits; return $ A.IntLiteral m d }
            <|> do { d <- lexeme (sHash >> many1 hexDigit); return $ A.HexLiteral m d }
    <?> "integer literal"

digits :: OccParser String
digits
    =   many1 digit
    <?> "decimal digits"

byte :: OccParser A.LiteralRepr
byte
    =  do m <- md
          char '\''
          c <- literalCharacter
          sApos
          return c
    <?> "byte literal"

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
          char '"'
          cs <- manyTill literalCharacter sQuote
          let aes = [A.ArrayElemExpr $ A.Literal m A.Byte c | c <- cs]
          return (A.ArrayLiteral m aes, A.Dimension $ length cs)
    <?> "string literal"

character :: OccParser String
character
    =   do char '*'
           do char '#'
              a <- hexDigit
              b <- hexDigit
              return $ ['*', '#', a, b]
            <|> do { c <- anyChar; return ['*', c] }
    <|> do c <- anyChar
           return [c]
    <?> "character"

literalCharacter :: OccParser A.LiteralRepr
literalCharacter
    =   do m <- md
           c <- character
           return $ A.ByteLiteral m c
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
          matchType tl tr
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
          matchType wantT t
          return e

intExpr = expressionOfType A.Int <?> "integer expression"
booleanExpr = expressionOfType A.Bool <?> "boolean expression"

constExprOfType :: A.Type -> OccParser A.Expression
constExprOfType wantT
    =  do e <- expressionOfType wantT
          (e', isConst, msg) <- constantFold e
          when (not isConst) $
            fail $ "expression is not constant (" ++ msg ++ ")"
          return e'

constIntExpr = constExprOfType A.Int <?> "constant integer expression"

operandOfType :: A.Type -> OccParser A.Expression
operandOfType wantT
    =  do o <- inTypeContext (Just wantT) operand
          t <- typeOfExpression o
          matchType wantT t
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
          matchTypes types rts
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
    =   do { reservedOp "-" <|> sMINUS; return A.MonadicSubtr }
    <|> do { reservedOp "~" <|> sBITNOT; return A.MonadicBitNot }
    <|> do { sNOT; return A.MonadicNot }
    <?> "monadic operator"

dyadicOperator :: OccParser A.DyadicOp
dyadicOperator
    =   do { reservedOp "+"; return A.Add }
    <|> do { reservedOp "-"; return A.Subtr }
    <|> do { reservedOp "*"; return A.Mul }
    <|> do { reservedOp "/"; return A.Div }
    <|> do { reservedOp "\\"; return A.Rem }
    <|> do { sREM; return A.Rem }
    <|> do { sMINUS; return A.Minus }
    <|> do { reservedOp "/\\" <|> sBITAND; return A.BitAnd }
    <|> do { reservedOp "\\/" <|> sBITOR; return A.BitOr }
    <|> do { reservedOp "><"; return A.BitXor }
    <?> "dyadic operator"

-- These always need an INT on their right-hand side.
shiftOperator :: OccParser A.DyadicOp
shiftOperator
    =   do { reservedOp "<<"; return A.LeftShift }
    <|> do { reservedOp ">>"; return A.RightShift }
    <?> "shift operator"

-- These always return a BOOL, so we have to deal with them specially for type
-- context.
comparisonOperator :: OccParser A.DyadicOp
comparisonOperator
    =   do { reservedOp "="; return A.Eq }
    <|> do { reservedOp "<>"; return A.NotEq }
    <|> do { reservedOp "<"; return A.Less }
    <|> do { reservedOp ">"; return A.More }
    <|> do { reservedOp "<="; return A.LessEq }
    <|> do { reservedOp ">="; return A.MoreEq }
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
          baseT <- underlyingType t
          (c, o) <- conversionMode
          ot <- typeOfExpression o
          baseOT <- underlyingType ot
          c <- case (isPreciseConversion baseOT baseT, c) of
                 (False, A.DefaultConversion) ->
                   fail "imprecise conversion must specify ROUND or TRUNC"
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
           do { o <- noTypeContext operand; sRightR; return $ A.BytesInExpr m o }
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
          matchType wantT t
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
          matchType wantT t
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
          matchType wantT t
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
           nd <- lookupName n
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
           matchType s t
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
             (A.Array _ (A.Chan _)) -> return ()
             _ -> fail $ "types do not match in channel array abbreviation"
           return $ A.Specification m n $ A.IsChannelArray m t cs
    <|> do m <- md
           (ct, s, n) <- try (do s <- channelSpecifier
                                 n <- newChannelName
                                 sIS
                                 sLeft
                                 ct <- trivialSubscriptType s
                                 case ct of
                                   A.Chan _ -> return (ct, s, n)
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
           do { sIS; fs' <- scopeInFormals fs; el <- expressionList rs; scopeOutFormals fs'; sColon; eol; return $ A.Specification m n $ A.Function m sm rs fs' (A.OnlyEL m el) }
             <|> do { eol; indent; fs' <- scopeInFormals fs; vp <- valueProcess rs; scopeOutFormals fs'; outdent; sColon; eol; return $ A.Specification m n $ A.Function m sm rs fs' vp }
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
           checkRetypes origT s
           return $ A.Specification m n $ A.Retypes m A.Abbrev s v
    <|> do m <- md
           (s, n) <- tryVVX channelSpecifier newChannelName retypesReshapes
           c <- channel
           sColon
           eol
           origT <- typeOfVariable c
           checkRetypes origT s
           return $ A.Specification m n $ A.Retypes m A.Abbrev s c
    <|> do m <- md
           (s, n) <- tryXVVX sVAL dataSpecifier newVariableName retypesReshapes
           e <- expression
           sColon
           eol
           origT <- typeOfExpression e
           checkRetypes origT s
           return $ A.Specification m n $ A.RetypesExpr m A.ValAbbrev s e
    <?> "RETYPES/RESHAPES abbreviation"

-- | Check that a RETYPES/RESHAPES is safe.
checkRetypes :: A.Type -> A.Type -> OccParser ()
-- Retyping channels is always "safe".
checkRetypes (A.Chan _) (A.Chan _) = return ()
checkRetypes fromT toT
    =  do bf <- bytesInType fromT
          bt <- bytesInType toT
          case (bf, bt) of
            (BIJust a, BIJust b) ->
              when (a /= b) $ fail "size mismatch in RETYPES"
            (BIJust a, BIOneFree b _) ->
              when (not ((b <= a) && (a `mod` b == 0))) $ fail "size mismatch in RETYPES"
            (_, BIManyFree) ->
              fail "multiple free dimensions in RETYPES/RESHAPES type"
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
  where aa = liftM (\t -> (A.Abbrev, t))

formalVariableType :: OccParser (A.AbbrevMode, A.Type)
formalVariableType
    =   do sVAL
           s <- dataSpecifier
           return (A.ValAbbrev, s)
    <|> do s <- dataSpecifier
           return (A.Abbrev, s)
    <?> "formal variable type"

valueProcess :: [A.Type] -> OccParser A.Structured
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
           return $ A.ProcThen m p (A.OnlyEL m el)
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
    <|> mainProcess
    <|> handleSpecs (allocation <|> specification) process
                    (\m s p -> A.Seq m (A.Spec m s (A.OnlyP m p)))
    <|> preprocessorDirective
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
                  return (c, A.InputCase m (A.OnlyV m (tl (A.Skip m))))
    <?> "channel input"

timerInput :: OccParser (A.Variable, A.InputMode)
timerInput
    =   do m <- md
           c <- tryVX timer sQuest
           do { v <- variableOfType A.Int; eol; return (c, A.InputSimple m [A.InVariable m v]) }
             <|> do { sAFTER; e <- intExpr; eol; return (c, A.InputAfter m e) }
    <?> "timer input"

taggedList :: [(A.Name, [A.Type])] -> OccParser (A.Process -> A.Variant)
taggedList nts
    =  do m <- md
          tag <- tagName
          ts <- checkJust "unknown tag in protocol" $ lookup tag nts
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
             w <- variableOfType (makeArrayType A.UnknownDimension it)
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
             Left _ -> fail "CASE input on channel of non-variant protocol"
             Right nts -> return nts

caseInput :: OccParser A.Process
caseInput
    =   do m <- md
           c <- tryVX channel (do {sQuest; sCASE; eol})
           nts <- caseInputItems c
           vs <- maybeIndentedList m "empty ? CASE" (variant nts)
           return $ A.Input m c (A.InputCase m (A.Several m vs))
    <?> "case input"

variant :: [(A.Name, [A.Type])] -> OccParser A.Structured
variant nts
    =   do m <- md
           tl <- taggedList nts
           eol
           indent
           p <- process
           outdent
           return $ A.OnlyV m (tl p)
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
                  ts <- checkJust "unknown tag in protocol" $ lookup tag nts
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
             b <- expressionOfType (makeArrayType A.UnknownDimension it)
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
           do { eol; ps <- maybeIndentedList m "empty SEQ" process; return $ A.Seq m (A.Several m (map (A.OnlyP m) ps)) }
             <|> do { r <- replicator; eol; indent; r' <- scopeInRep r; p <- process; scopeOutRep r'; outdent; return $ A.Seq m (A.Rep m r' (A.OnlyP m p)) }
    <?> "SEQ process"
--}}}
--{{{ IF
ifProcess :: OccParser A.Process
ifProcess
    =   do m <- md
           c <- conditional
           return $ A.If m c
    <?> "IF process"

conditional :: OccParser A.Structured
conditional
    =   do m <- md
           sIF
           do { eol; cs <- maybeIndentedList m "empty IF" ifChoice; return $ A.Several m cs }
             <|> do { r <- replicator; eol; indent; r' <- scopeInRep r; c <- ifChoice; scopeOutRep r'; outdent; return $ A.Rep m r' c }
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
    <?> "guarded choice"
--}}}
--{{{ CASE
caseProcess :: OccParser A.Process
caseProcess
    =   do m <- md
           sCASE
           sel <- expression
           t <- typeOfExpression sel
           t' <- underlyingType t
           when (not $ isCaseableType t') $ fail "case selector has non-CASEable type"
           eol
           os <- maybeIndentedList m "empty CASE" (caseOption t)
           return $ A.Case m sel (A.Several m os)
    <?> "CASE process"

caseOption :: A.Type -> OccParser A.Structured
caseOption t
    =   do m <- md
           ces <- tryVX (sepBy (constExprOfType t) sComma) eol
           indent
           p <- process
           outdent
           return $ A.OnlyO m (A.Option m ces p)
    <|> do m <- md
           sELSE
           eol
           indent
           p <- process
           outdent
           return $ A.OnlyO m (A.Else m p)
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
           do { eol; ps <- maybeIndentedList m "empty PAR" process; return $ A.Par m isPri (A.Several m (map (A.OnlyP m) ps)) }
             <|> do { r <- replicator; eol; indent; r' <- scopeInRep r; p <- process; scopeOutRep r'; outdent; return $ A.Par m isPri (A.Rep m r' (A.OnlyP m p)) }
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

alternation :: OccParser (Bool, A.Structured)
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
alternative :: OccParser A.Structured
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
           return $ A.OnlyA m (A.AlternativeCond m b c (A.InputCase m $ A.Several m vs) (A.Skip m))
    <|> do m <- md
           c <- tryVXX channel sQuest (sCASE >> eol)
           nts <- caseInputItems c
           vs <- maybeIndentedList m "empty ? CASE" (variant nts)
           return $ A.OnlyA m (A.Alternative m c (A.InputCase m $ A.Several m vs) (A.Skip m))
    <|> guardedAlternative
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
                A.Chan _ -> var (channelOfType t)
                A.Timer -> var timer
                A.Port _ -> var (portOfType t)
                _ -> var (variableOfType t)
    <?> "actual of type " ++ show t ++ " for " ++ show n
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
--{{{ preprocessor directives
preprocessorDirective :: OccParser A.Process
preprocessorDirective
    =   ppInclude
    <|> ppUse
    <|> unknownPP
    <?> "preprocessor directive"

ppInclude :: OccParser A.Process
ppInclude
    =  do sppINCLUDE
          char '"'
          file <- manyTill character sQuote
          eol
          includeFile $ concat file
    <?> "#INCLUDE directive"

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
    <?> "#USE directive"

-- | Invoke the parser recursively to handle an included file.
includeFile :: String -> OccParser A.Process
includeFile file
    =  do ps <- getState
          (r, ps') <- parseFile file includedFile ps
          case r of
            Left p ->
              do setState ps'
                 return p
            Right f ->
              do setState ps' { psLocalNames = psMainLocals ps' }
                 p <- process
                 return $ f p

unknownPP :: OccParser A.Process
    =  do m <- md
          char '#'
          rest <- manyTill anyChar (try eol)
          addWarning m $ "unknown preprocessor directive ignored: " ++ rest
          process
    <?> "unknown preprocessor directive"
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
-- | A source file consists of a process.
-- This is only really true once we've tacked a process onto the bottom; a
-- source file is really a series of specifications, but the later ones need to
-- have the earlier ones in scope, so we can't parse them separately.
sourceFile :: OccParser (A.Process, ParseState)
sourceFile
    =   do whiteSpace
           p <- process
           s <- getState
           return (p, s)

-- | An included file is either a process, or a bunch of specs that can be
-- applied to a process (which we return as a function). This is likewise a bit
-- of a cheat, in that included files should really be *textually* included,
-- but it's good enough for most reasonable uses.
includedFile :: OccParser (Either A.Process (A.Process -> A.Process), ParseState)
includedFile
    =  do whiteSpace
          p <- process
          s <- getState
          do eof
             return $ (Right $ replaceMain p, s)
           <|> do sMainMarker
                  eol
                  return $ (Left p, s)
  where
    replaceMain :: A.Process -> A.Process -> A.Process
    replaceMain (A.Seq m (A.Spec m' s (A.OnlyP m'' p))) np
        = A.Seq m (A.Spec m' s (A.OnlyP m'' (replaceMain p np)))
    replaceMain (A.Main _) np = np
--}}}
--}}}

--{{{  preprocessor
-- XXX Doesn't handle conditionals.

readSource :: String -> IO String
readSource file
    =  do f <- IO.openFile file IO.ReadMode
          IO.hGetContents f

-- | Find (via a nasty regex search) all the files that this source file includes.
preFindIncludes :: String -> [String]
preFindIncludes source
    = concat [case matchRegex incRE l of
                Just [_, fn] -> [fn]
                Nothing -> []
              | l <- lines source]
  where
    incRE = mkRegex "^ *#(INCLUDE|USE) +\"([^\"]*)\""

-- | If a module name doesn't already have a suffix, add one.
mangleModName :: String -> String
mangleModName mod
    = if ".occ" `isSuffixOf` mod || ".inc" `isSuffixOf` mod
        then mod
        else mod ++ ".occ"

-- | Load all the source files necessary for a program.
-- We have to do this now, before entering the parser, because the parser
-- doesn't run in the IO monad. If there were a monad transformer version of
-- Parsec then we could just open files as we need them.
loadSource :: String -> PassM ()
loadSource file = load file file
  where
    load :: String -> String -> PassM ()
    load file realName
        =  do ps <- get
              case Map.lookup file (psSourceFiles ps) of
                Just _ -> return ()
                Nothing ->
                  do progress $ "Loading source file " ++ realName
                     rawSource <- liftIO $ readSource realName
                     source <- removeIndentation realName (rawSource ++ "\n" ++ mainMarker ++ "\n")
                     debug $ "Preprocessed source:"
                     debug $ numberLines source
                     modify $ (\ps -> ps { psSourceFiles = Map.insert file source (psSourceFiles ps) })
                     let deps = map mangleModName $ preFindIncludes source
                     sequence_ [load dep (joinPath realName dep) | dep <- deps]
--}}}

--{{{  entry points for the parser itself
-- | Test a parser production (for use from ghci while debugging the parser).
testParse :: Show a => OccParser a -> String -> IO ()
testParse prod text
    = do let r = runParser prod emptyState "" text
         putStrLn $ "Result: " ++ show r

-- | Parse a file with the given production.
parseFile :: Monad m => String -> OccParser t -> ParseState -> m t
parseFile file prod ps
    =  do let source = case Map.lookup file (psSourceFiles ps) of
                         Just s -> s
                         Nothing -> dieIO $ "Failed to preload file: " ++ show file
          let ps' = ps { psLoadedFiles = file : psLoadedFiles ps }
          case runParser prod ps' file source of
            Left err -> dieIO $ "Parse error: " ++ show err
            Right r -> return r

-- | Parse the top level source file in a program.
parseProgram :: String -> PassM A.Process
parseProgram file
    =  do ps <- get
          (p, ps') <- parseFile file sourceFile ps
          put ps'
          return p
--}}}

