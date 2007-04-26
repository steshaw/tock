-- | Generate C code from the mangled AST.
module GenerateC where

import Data.List
import Data.Maybe
import Control.Monad.Writer
import Control.Monad.Error
import Control.Monad.State
import Numeric
import Text.Printf

import qualified AST as A
import Metadata
import ParseState
import Pass
import Errors
import TLP
import Types

--{{{  monad definition
type CGen = WriterT [String] PassM

instance Die CGen where
  die = throwError
--}}}

--{{{  top-level
generateC :: A.Process -> PassM String
generateC ast
    =  do (a, w) <- runWriterT (genTopLevel ast)
          return $ concat w

genTLPChannel :: TLPChannel -> CGen ()
genTLPChannel TLPIn = tell ["in"]
genTLPChannel TLPOut = tell ["out"]
genTLPChannel TLPError = tell ["err"]

genTopLevel :: A.Process -> CGen ()
genTopLevel p
    =  do tell ["#include <fco_support.h>\n"]
          genProcess p
          (name, chans) <- tlpInterface
          tell ["void fco_main (Process *me, Channel *in, Channel *out, Channel *err) {\n"]
          genName name
          tell [" (me"]
          sequence_ [tell [", "] >> genTLPChannel c | c <- chans]
          tell [");\n"]
          tell ["}\n"]
--}}}

--{{{  utilities
missing :: String -> CGen ()
missing s = tell ["\n#error Unimplemented: ", s, "\n"]

genComma :: CGen ()
genComma = tell [", "]

checkJust :: MonadError String m => Maybe t -> m t
checkJust (Just v) = return v
checkJust Nothing = throwError "checkJust failed"

type SubscripterFunction = A.Variable -> A.Variable

overArray :: A.Variable -> (SubscripterFunction -> Maybe (CGen ())) -> CGen ()
overArray var func
    =  do A.Array ds _ <- typeOfVariable var
          let m = emptyMeta
          specs <- sequence [makeNonceVariable "i" m A.Int A.VariableName A.Original | _ <- ds]
          let indices = [A.Variable m n | A.Specification _ n _ <- specs]

          let arg = (\var -> foldl (\v s -> A.SubscriptedVariable m s v) var [A.Subscript m $ A.ExprVariable m i | i <- indices])
          case func arg of
            Just p ->
              do sequence_ [do tell ["for (int "]
                               genVariable i
                               tell [" = 0; "]
                               genVariable i
                               tell [" < "]
                               genVariable var
                               tell ["_sizes[", show v, "]; "]
                               genVariable i
                               tell ["++) {\n"]
                            | (v, i) <- zip [0..] indices]
                 p
                 sequence_ [tell ["}\n"] | _ <- indices]
            Nothing -> return ()

-- | Generate code for one of the Structured types.
genStructured :: A.Structured -> (A.Structured -> CGen ()) -> CGen ()
genStructured (A.Rep _ rep s) def = genReplicator rep (genStructured s def)
genStructured (A.Spec _ spec s) def = genSpec spec (genStructured s def)
genStructured (A.Several _ ss) def = sequence_ [genStructured s def | s <- ss]
genStructured s def = def s

data InputType = ITTimerRead | ITTimerAfter | ITOther

inputType :: A.Variable -> A.InputMode -> CGen InputType
inputType c im
    =  do t <- typeOfVariable c
          return $ case t of
                     A.Timer ->
                       case im of
                         A.InputSimple _ _ -> ITTimerRead
                         A.InputAfter _ _ -> ITTimerAfter
                     _ -> ITOther
--}}}

--{{{  metadata
genMeta :: Meta -> CGen ()
genMeta m = tell ["\"", show m, "\""]
--}}}

--{{{  names
genName :: A.Name -> CGen ()
genName n = tell [[if c == '.' then '_' else c | c <- A.nameName n]]
--}}}

--{{{  types
scalarType :: A.Type -> Maybe String
scalarType A.Bool = Just "bool"
-- FIXME: This probably isn't right; we might have to explicitly cast string literals...
scalarType A.Byte = Just "char"
scalarType A.Int = Just "int"
scalarType A.Int16 = Just "int16_t"
scalarType A.Int32 = Just "int32_t"
scalarType A.Int64 = Just "int64_t"
scalarType A.Real32 = Just "float"
scalarType A.Real64 = Just "double"
scalarType A.Timer = Just "Time"
scalarType _ = Nothing

genType :: A.Type -> CGen ()
genType (A.Array _ t)
    =  do genType t
          tell ["*"]
genType (A.UserDataType n) = genName n
-- UserProtocol -- not used
genType (A.Chan t) = tell ["Channel *"]
-- Counted -- not used
-- Any -- not used
--genType (A.Port t) =
genType t
    = case scalarType t of
        Just s -> tell [s]
        Nothing -> missing $ "genType " ++ show t

genBytesInType :: A.Type -> CGen ()
genBytesInType (A.Array ds t) = genBytesInDims ds >> genBytesInType t
  where
    genBytesInDims [] = return ()
    genBytesInDims ((A.Dimension n):ds)
        = genBytesInDims ds >> tell [show n, " * "]
    genBytesInDims _ = missing "genBytesInType with empty dimension"
--bytesInType (A.UserDataType n)
genBytesInType t
    = case scalarType t of
        Just s -> tell ["sizeof (", s, ")"]
        Nothing -> missing $ "genBytesInType " ++ show t
--}}}

--{{{  declarations
genDeclType :: A.AbbrevMode -> A.Type -> CGen ()
genDeclType am t
    =  do when (am == A.ValAbbrev) $ tell ["const "]
          genType t
          case t of
            A.Array _ _ -> return ()
            A.Chan _ -> return ()
            A.UserDataType _ -> tell [" *"]
            _ -> when (am == A.Abbrev) $ tell [" *"]

genDecl :: A.AbbrevMode -> A.Type -> A.Name -> CGen ()
genDecl am t n
    =  do genDeclType am t
          tell [" "]
          genName n
--}}}

--{{{  conversions
genConversion :: Meta -> A.ConversionMode -> A.Type -> A.Expression -> CGen ()
genConversion m A.DefaultConversion t e
    =  do tell ["(("]
          genType t
          tell [") "]
          origT <- typeOfExpression e
          if isSafeConversion origT t
            then genExpression e
            else do genTypeSymbol "range_check" origT
                    tell [" ("]
                    genTypeSymbol "mostneg" t
                    tell [", "]
                    genTypeSymbol "mostpos" t
                    tell [", "]
                    genExpression e
                    tell [", "]
                    genMeta m
                    tell [")"]
          tell [")"]
genConversion m cm t e = missing $ "genConversion " ++ show cm
--}}}

--{{{  literals
genLiteral :: A.Literal -> CGen ()
genLiteral (A.Literal m t lr) = genLiteralRepr lr
genLiteral l = missing $ "genLiteral " ++ show l

genLiteralRepr :: A.LiteralRepr -> CGen ()
genLiteralRepr (A.RealLiteral m s) = tell [s]
genLiteralRepr (A.IntLiteral m s) = genDecimal s
genLiteralRepr (A.HexLiteral m s) = tell ["0x", s]
genLiteralRepr (A.ByteLiteral m s) = tell ["'", convStringLiteral s, "'"]
genLiteralRepr (A.StringLiteral m s) = tell ["\"", convStringLiteral s, "\""]
genLiteralRepr (A.ArrayLiteral m aes)
    =  do tell ["{"]
          genArrayLiteralElems aes
          tell ["}"]

-- | Generate a decimal literal -- removing leading zeroes to avoid producing
-- an octal literal!
genDecimal :: String -> CGen ()
genDecimal "0" = tell ["0"]
genDecimal ('0':s) = genDecimal s
genDecimal ('-':s) = tell ["-"] >> genDecimal s
genDecimal s = tell [s]

genArrayLiteralElems :: [A.ArrayElem] -> CGen ()
genArrayLiteralElems aes
    = sequence_ $ intersperse genComma $ map genElem aes
  where
    genElem :: A.ArrayElem -> CGen ()
    genElem (A.ArrayElemArray aes) = genArrayLiteralElems aes
    genElem (A.ArrayElemExpr e)
        =  do t <- typeOfExpression e
              case t of
                A.Array _ _ -> missing $ "array literal containing non-literal array: " ++ show e
                _ -> genExpression e

hexToOct :: String -> String
hexToOct h = printf "%03o" ((fst $ head $ readHex h) :: Int)

convStringLiteral :: String -> String
convStringLiteral [] = []
convStringLiteral ('\\':s) = "\\\\" ++ convStringLiteral s
convStringLiteral ('*':'#':'0':'0':s) = "\\0" ++ convStringLiteral s
convStringLiteral ('*':'#':a:b:s) = "\\" ++ hexToOct [a, b] ++ convStringLiteral s
convStringLiteral ('*':c:s) = convStringStar c ++ convStringLiteral s
convStringLiteral (c:s) = c : convStringLiteral s

convStringStar :: Char -> String
convStringStar 'c' = "\\r"
convStringStar 'n' = "\\n"
convStringStar 't' = "\\t"
convStringStar 's' = " "
convStringStar c = [c]
--}}}

--{{{  variables
{-
The various types are generated like this:

                        ================= Use =================
                        Original        ValAbbrev   Abbrev
                        --------------------------------------
INT x:                  int x;          int x;      int *x;
  x                     x               x           *x

[10]INT xs:             int xs[10];     int *xs;    int *xs;
  xs                    xs              xs          xs
  xs[i]                 xs[i]           xs[i]       xs[i]

[20][10]INT xss:        int xss[20*10]; int *xss;   int *xss;
  xss                   xss             xss         xss
  xss[i]                &xss[i*10]      &xss[i*10]  &xss[i*10]  (where 10 = xss_sizes[1])
  xss[i][j]             xss[i*10+j]     xss[i*10+j] xss[i*10+j]

[6][4][2]INT xsss:      int xsss[6*4*2]; int *xsss;
  xsss                  xsss             (as left)
  xsss[i]               &xsss[i*4*2]
  xsss[i][j]            &xsss[i*4*2+j*2]
  xsss[i][j][k]         xsss[i*4*2+j*2+k]

MYREC r:                MYREC r;        MYREC *r;   MYREC *r;
  r                     &r              r           r
  r[F]                  (&r)->F         (r)->F      (r)->F

[10]MYREC rs:           MYREC rs[10];   MYREC *rs;  MYREC *rs;
  rs                    rs              rs          rs
  rs[i]                 &rs[i]          &rs[i]      &rs[i]
  rs[i][F]              (&rs[i])->F     (&rs[i])->F (&rs[i])->F
                           -- depending on what F is -- if it's another record...

CHAN OF INT c:          Channel c;                  Channel *c;
  c                     &c                          c

[10]CHAN OF INT cs:     Channel **cs;               Channel **cs;
  cs                    cs                          cs
  cs[i]                 cs[i]                       cs[i]

I suspect there's probably a nicer way of doing this, but as a translation of
the above table this isn't too horrible...
-}
genVariable :: A.Variable -> CGen ()
genVariable v
    =  do am <- abbrevModeOfVariable v
          t <- typeOfVariable v
          let isSub = case v of
                        A.Variable _ _ -> False
                        A.SubscriptedVariable _ _ _ -> True

          let prefix = case (am, t) of
                         (_, A.Array _ _) -> ""
                         (A.Original, A.Chan _) -> if isSub then "" else "&"
                         (A.Abbrev, A.Chan _) -> ""
                         (A.Original, A.UserDataType _) -> "&"
                         (A.Abbrev, A.UserDataType _) -> ""
                         (A.Abbrev, _) -> "*"
                         _ -> ""

          when (prefix /= "") $ tell ["(", prefix]
          inner v
          when (prefix /= "") $ tell [")"]
  where
    inner :: A.Variable -> CGen ()
    inner (A.Variable _ n) = genName n
    inner sv@(A.SubscriptedVariable _ (A.Subscript _ _) _)
        =  do let (es, v) = collectSubs sv
              genVariable v
              genArraySubscript v es
    inner (A.SubscriptedVariable _ (A.SubscriptField m n) v)
        =  do genVariable v
              tell ["->"]
              genName n
    inner (A.SubscriptedVariable m (A.SubscriptFromFor m' start _) v)
        = inner (A.SubscriptedVariable m (A.Subscript m' start) v)
    inner (A.SubscriptedVariable m (A.SubscriptFrom m' start) v)
        = inner (A.SubscriptedVariable m (A.Subscript m' start) v)
    inner (A.SubscriptedVariable m (A.SubscriptFor m' _) v)
        = inner (A.SubscriptedVariable m (A.Subscript m' (makeConstant m' 0)) v)

    -- | Collect all the plain subscripts on a variable, so we can combine them.
    collectSubs :: A.Variable -> ([A.Expression], A.Variable)
    collectSubs (A.SubscriptedVariable _ (A.Subscript _ e) v)
        = (es' ++ [e], v')
      where
        (es', v') = collectSubs v
    collectSubs v = ([], v)

genArraySubscript :: A.Variable -> [A.Expression] -> CGen ()
genArraySubscript v es
    =  do t <- typeOfVariable v
          let numDims = case t of A.Array ds _ -> length ds
          tell ["["]
          sequence_ $ intersperse (tell [" + "]) $ genPlainSub v es [0..(numDims - 1)]
          tell ["]"]
  where
    -- | Generate the individual offsets that need adding together to find the
    -- right place in the array.
    -- FIXME This is obviously not the best way to factor this, but I figure a
    -- smart C compiler should be able to work it out...
    genPlainSub :: A.Variable -> [A.Expression] -> [Int] -> [CGen ()]
    genPlainSub _ [] _ = []
    genPlainSub v (e:es) (sub:subs)
        = gen : genPlainSub v es subs
      where
        gen = sequence_ $ intersperse (tell [" * "]) $ genSub : genChunks
        genSub
            = do tell ["occam_check_index ("]
                 genExpression e
                 tell [", "]
                 genVariable v
                 tell ["_sizes[", show sub, "], "]
                 genMeta (metaOfExpression e)
                 tell [")"]
        genChunks = [genVariable v >> tell ["_sizes[", show i, "]"] | i <- subs]
--}}}

--{{{  expressions
genExpression :: A.Expression -> CGen ()
genExpression (A.Monadic m op e) = genMonadic m op e
genExpression (A.Dyadic m op e f) = genDyadic m op e f
genExpression (A.MostPos m t) = genTypeSymbol "mostpos" t
genExpression (A.MostNeg m t) = genTypeSymbol "mostneg" t
--genExpression (A.SizeType m t)
genExpression (A.SizeExpr m e)
    =  do genExpression e
          tell ["_sizes[0]"]
genExpression (A.SizeVariable m v)
    =  do genVariable v
          tell ["_sizes[0]"]
genExpression (A.Conversion m cm t e) = genConversion m cm t e
genExpression (A.ExprVariable m v) = genVariable v
genExpression (A.ExprLiteral m l) = genLiteral l
genExpression (A.True m) = tell ["true"]
genExpression (A.False m) = tell ["false"]
--genExpression (A.FunctionCall m n es)
--genExpression (A.SubscriptedExpr m s e)
--genExpression (A.BytesInExpr m e)
genExpression (A.BytesInType m t) = genBytesInType t
--genExpression (A.OffsetOf m t n)
genExpression t = missing $ "genExpression " ++ show t

genTypeSymbol :: String -> A.Type -> CGen ()
genTypeSymbol s t
    = case scalarType t of
        Just ct -> tell ["occam_", s, "_", ct]
        Nothing -> missing $ "genTypeSymbol " ++ show t
--}}}

--{{{  operators
genSimpleMonadic :: String -> A.Expression -> CGen ()
genSimpleMonadic s e
    =  do tell ["(", s]
          genExpression e
          tell [")"]

genMonadic :: Meta -> A.MonadicOp -> A.Expression -> CGen ()
genMonadic _ A.MonadicSubtr e = genSimpleMonadic "-" e
genMonadic _ A.MonadicBitNot e = genSimpleMonadic "~" e
genMonadic _ A.MonadicNot e = genSimpleMonadic "!" e

genSimpleDyadic :: String -> A.Expression -> A.Expression -> CGen ()
genSimpleDyadic s e f
    =  do tell ["("]
          genExpression e
          tell [" ", s, " "]
          genExpression f
          tell [")"]

genFuncDyadic :: Meta -> String -> A.Expression -> A.Expression -> CGen ()
genFuncDyadic m s e f
    =  do t <- typeOfExpression e
          genTypeSymbol s t
          tell [" ("]
          genExpression e
          tell [", "]
          genExpression f
          tell [", "]
          genMeta m
          tell [")"]

genDyadic :: Meta -> A.DyadicOp -> A.Expression -> A.Expression -> CGen ()
genDyadic m A.Add e f = genFuncDyadic m "add" e f
genDyadic m A.Subtr e f = genFuncDyadic m "subtr" e f
genDyadic m A.Mul e f = genFuncDyadic m "mul" e f
genDyadic m A.Div e f = genFuncDyadic m "div" e f
genDyadic m A.Rem e f = genFuncDyadic m "rem" e f
genDyadic _ A.Plus e f = genSimpleDyadic "+" e f
genDyadic _ A.Minus e f = genSimpleDyadic "-" e f
genDyadic _ A.Times e f = genSimpleDyadic "*" e f
genDyadic _ A.LeftShift e f = genSimpleDyadic "<<" e f
genDyadic _ A.RightShift e f = genSimpleDyadic ">>" e f
genDyadic _ A.BitAnd e f = genSimpleDyadic "&" e f
genDyadic _ A.BitOr e f = genSimpleDyadic "|" e f
genDyadic _ A.BitXor e f = genSimpleDyadic "^" e f
genDyadic _ A.And e f = genSimpleDyadic "&&" e f
genDyadic _ A.Or e f = genSimpleDyadic "||" e f
genDyadic _ A.Eq e f = genSimpleDyadic "==" e f
genDyadic _ A.NotEq e f = genSimpleDyadic "!=" e f
genDyadic _ A.Less e f = genSimpleDyadic "<" e f
genDyadic _ A.More e f = genSimpleDyadic ">" e f
genDyadic _ A.LessEq e f = genSimpleDyadic "<=" e f
genDyadic _ A.MoreEq e f = genSimpleDyadic ">=" e f
--}}}

--{{{  input/output items
genInputItem :: A.Variable -> A.InputItem -> CGen ()
genInputItem c (A.InCounted m cv av)
    =  do genInputItem c (A.InVariable m cv)
          t <- typeOfVariable av
          tell ["ChanIn ("]
          genVariable c
          tell [", "]
          fst $ abbrevVariable A.Abbrev t av
          tell [", "]
          subT <- subscriptType (A.Subscript m $ makeConstant m 0) t
          genVariable cv
          tell [" * "]
          genBytesInType subT
          tell [");\n"]
genInputItem c (A.InVariable m v)
    =  do t <- typeOfVariable v
          let rhs = fst $ abbrevVariable A.Abbrev t v
          case t of
            A.Int ->
              do tell ["ChanInInt ("]
                 genVariable c
                 tell [", "]
                 rhs
                 tell [");\n"]
            _ ->
              do tell ["ChanIn ("]
                 genVariable c
                 tell [", "]
                 rhs
                 tell [", "]
                 genBytesInType t
                 tell [");\n"]

genOutputItem :: A.Variable -> A.OutputItem -> CGen ()
genOutputItem c (A.OutCounted m ce ae)
    =  do genOutputItem c (A.OutExpression m ce)
          t <- typeOfExpression ae
          case ae of
            A.ExprVariable m v ->
              do tell ["ChanOut ("]
                 genVariable c
                 tell [", "]
                 fst $ abbrevVariable A.Abbrev t v
                 tell [", "]
                 subT <- subscriptType (A.Subscript m $ makeConstant m 0) t
                 genExpression ce
                 tell [" * "]
                 genBytesInType subT
                 tell [");\n"]
genOutputItem c (A.OutExpression m e)
    =  do t <- typeOfExpression e
          case (t, e) of
            (A.Int, _) ->
              do tell ["ChanOutInt ("]
                 genVariable c
                 tell [", "]
                 genExpression e
                 tell [");\n"]
            (_, A.ExprVariable _ v) ->
              do tell ["ChanOut ("]
                 genVariable c
                 tell [", "]
                 fst $ abbrevVariable A.Abbrev t v
                 tell [", "]
                 genBytesInType t
                 tell [");\n"]
            _ ->
              do n <- makeNonce "output_item"
                 tell ["const "]
                 genType t
                 tell [" ", n, " = "]
                 genExpression e
                 tell [";\n"]
                 tell ["ChanOut ("]
                 genVariable c
                 tell [", &", n, ", "]
                 genBytesInType t
                 tell [");\n"]
--}}}

--{{{  replicators
genReplicator :: A.Replicator -> CGen () -> CGen ()
genReplicator rep body
    =  do tell ["for ("]
          genReplicatorLoop rep
          tell [") {\n"]
          body
          tell ["}\n"]

isZero :: A.Expression -> Bool
isZero (A.ExprLiteral _ (A.Literal _ A.Int (A.IntLiteral _ "0"))) = True
isZero _ = False

genReplicatorLoop :: A.Replicator -> CGen ()
genReplicatorLoop (A.For m index base count)
    = if isZero base
        then genSimpleReplicatorLoop index count
        else genGeneralReplicatorLoop index base count

genSimpleReplicatorLoop :: A.Name -> A.Expression -> CGen ()
genSimpleReplicatorLoop index count
    =  do tell ["int "]
          genName index
          tell [" = 0; "]
          genName index
          tell [" < "]
          genExpression count
          tell ["; "]
          genName index
          tell ["++"]

genGeneralReplicatorLoop :: A.Name -> A.Expression -> A.Expression -> CGen ()
genGeneralReplicatorLoop index base count
    =  do counter <- makeNonce "replicator_count"
          tell ["int ", counter, " = "]
          genExpression count
          tell [", "]
          genName index
          tell [" = "]
          genExpression base
          tell ["; ", counter, " > 0; ", counter, "--, "]
          genName index
          tell ["++"]

genReplicatorSize :: A.Replicator -> CGen ()
genReplicatorSize (A.For m n base count) = genExpression count
--}}}

--{{{  choice/alternatives/options/variants
--}}}

--{{{  structured
--}}}

--{{{  abbreviations
-- FIXME: This code is horrible, and I can't easily convince myself that it's correct.

genSlice :: A.Variable -> A.Variable -> A.Expression -> A.Expression -> [A.Dimension] -> (CGen (), A.Name -> CGen ())
genSlice v (A.Variable _ on) start count ds
    = (tell ["&"] >> genVariable v,
       genArraySize False
                    (do tell ["occam_check_slice ("]
                        genExpression start
                        tell [", "]
                        genExpression count
                        tell [", "]
                        genName on
                        tell ["_sizes[0], "]
                        genMeta (metaOfExpression count)
                        tell [")"]
                        sequence_ [do tell [", "]
                                      genName on
                                      tell ["_sizes[", show i, "]"]
                                   | i <- [1..(length ds - 1)]]))

genArrayAbbrev :: A.Variable -> (CGen (), A.Name -> CGen ())
genArrayAbbrev v
    = (tell ["&"] >> genVariable v, genAASize v 0)
  where
    genAASize (A.SubscriptedVariable _ (A.Subscript _ _) v) arg
        = genAASize v (arg + 1)
    genAASize (A.Variable _ on) arg
        = genArraySize True
                       (tell ["&"] >> genName on >> tell ["_sizes[", show arg, "]"])

genArraySize :: Bool -> CGen () -> A.Name -> CGen ()
genArraySize isPtr size n
    = if isPtr
        then do tell ["const int *"]
                genName n
                tell ["_sizes = "]
                size
                tell [";\n"]
        else do tell ["const int "]
                genName n
                tell ["_sizes[] = { "]
                size
                tell [" };\n"]

noSize :: A.Name -> CGen ()
noSize n = return ()

genVariableAM :: A.Variable -> A.AbbrevMode -> CGen ()
genVariableAM v am
    =  do when (am == A.Abbrev) $ tell ["&"]
          genVariable v

-- | Generate the right-hand side of an abbreviation of a variable.
abbrevVariable :: A.AbbrevMode -> A.Type -> A.Variable -> (CGen (), A.Name -> CGen ())
abbrevVariable am (A.Array _ _) v@(A.SubscriptedVariable _ (A.Subscript _ _) _)
    = genArrayAbbrev v
abbrevVariable am (A.Array ds _) v@(A.SubscriptedVariable _ (A.SubscriptFromFor _ start count) v')
    = genSlice v v' start count ds
abbrevVariable am (A.Array ds _) v@(A.SubscriptedVariable m (A.SubscriptFrom _ start) v')
    = genSlice v v' start (A.Dyadic m A.Minus (A.SizeExpr m (A.ExprVariable m v')) start) ds
abbrevVariable am (A.Array ds _) v@(A.SubscriptedVariable m (A.SubscriptFor _ count) v')
    = genSlice v v' (makeConstant m 0) count ds
abbrevVariable am (A.Array _ _) v
    = (genVariable v, genArraySize True (genVariable v >> tell ["_sizes"]))
abbrevVariable am (A.Chan _) v
    = (genVariable v, noSize)
abbrevVariable am (A.UserDataType _) v
    = (genVariable v, noSize)
abbrevVariable am t v
    = (genVariableAM v am, noSize)

-- | Generate the right-hand side of an abbreviation of an expression.
abbrevExpression :: A.AbbrevMode -> A.Type -> A.Expression -> (CGen (), A.Name -> CGen ())
abbrevExpression am t@(A.Array _ _) e
    = case e of
        A.ExprVariable _ v -> abbrevVariable am t v
        A.ExprLiteral _ l ->
          case l of
            A.Literal _ litT r -> (genExpression e, genTypeSize litT)
            A.SubscriptedLiteral _ _ _ -> bad
        _ -> bad
  where
    bad = (missing "array expression abbreviation", noSize)

    genTypeSize :: A.Type -> (A.Name -> CGen ())
    genTypeSize (A.Array ds _)
        = genArraySize False $ sequence_ $ intersperse genComma [tell [show n] | A.Dimension n <- ds]
abbrevExpression am _ e
    = (genExpression e, noSize)
--}}}

--{{{  specifications
genSpec :: A.Specification -> CGen () -> CGen ()
genSpec spec body
    =  do introduceSpec spec
          body
          removeSpec spec

-- | Generate the C type corresponding to a variable being declared.
-- It must be possible to use this in arrays.
declareType :: A.Type -> CGen ()
declareType (A.Chan _) = tell ["Channel *"]
declareType t = genType t

genDimensions :: [A.Dimension] -> CGen ()
genDimensions ds
    =  do tell ["["]
          sequence $ intersperse (tell [" * "])
                                 [case d of A.Dimension n -> tell [show n] | d <- ds]
          tell ["]"]

genDeclaration :: A.Type -> A.Name -> CGen ()
genDeclaration (A.Chan _) n
    =  do tell ["Channel "]
          genName n
          tell [";\n"]
genDeclaration (A.Array ds t) n
    =  do declareType t
          tell [" "]
          genName n
          genDimensions ds
          tell [";\n"]
genDeclaration t n
    =  do declareType t
          tell [" "]
          genName n
          tell [";\n"]

declareArraySizes :: [A.Dimension] -> CGen () -> CGen ()
declareArraySizes ds name
    =  do tell ["const int "]
          name
          tell ["_sizes[] = { "]
          sequence_ $ intersperse genComma [tell [show n] | A.Dimension n <- ds]
          tell [" };\n"]

-- | Initialise an item being declared.
declareInit :: A.Type -> A.Variable -> Maybe (CGen ())
declareInit (A.Chan _) var
    = Just $ do tell ["ChanInit ("]
                genVariable var
                tell [");\n"]
declareInit t@(A.Array ds t') var
    = Just $ do init <- case t' of
                          A.Chan _ ->
                            do let m = emptyMeta
                               A.Specification _ store _ <- makeNonceVariable "storage" m (A.Array ds A.Int) A.VariableName A.Original
                               let storeV = A.Variable m store
                               tell ["Channel "]
                               genName store
                               genDimensions ds
                               tell [";\n"]
                               declareArraySizes ds (genName store)
                               return (\sub -> Just $ do genVariable (sub var)
                                                         tell [" = &"]
                                                         genVariable (sub storeV)
                                                         tell [";\n"]
                                                         fromJust $ declareInit t' (sub var))
                          _ -> return (\sub -> declareInit t' (sub var))
                overArray var init
declareInit _ _ = Nothing

-- | Free a declared item that's going out of scope.
declareFree :: A.Type -> A.Variable -> Maybe (CGen ())
declareFree _ _ = Nothing

{-
                  Original        Abbrev
INT x IS y:       int *x = &y;    int *x = &(*y);
[]INT xs IS ys:   int *xs = ys;   int *xs = ys;
                  const int xs_sizes[] = ys_sizes;

CHAN OF INT c IS d:       Channel *c = d;

[10]CHAN OF INT cs:       Channel tmp[10];
                          Channel *cs[10];
                          for (...) { cs[i] = &tmp[i]; ChanInit(cs[i]); }
                          const int cs_sizes[] = { 10 };
[]CHAN OF INT ds IS cs:   Channel **ds = cs;
                          const int *ds_sizes = cs_sizes;
-}
introduceSpec :: A.Specification -> CGen ()
introduceSpec (A.Specification m n (A.Declaration _ t))
    = do genDeclaration t n
         case t of
           A.Array ds _ -> declareArraySizes ds (genName n)
           _ -> return ()
         case declareInit t (A.Variable m n) of
           Just p -> p
           Nothing -> return ()
introduceSpec (A.Specification _ n (A.Is _ am t v))
    =  do let (rhs, rhsSizes) = abbrevVariable am t v
          genDecl am t n
          tell [" = "]
          rhs
          tell [";\n"]
          rhsSizes n
introduceSpec (A.Specification _ n (A.IsExpr _ am t e))
    =  do let (rhs, rhsSizes) = abbrevExpression am t e
          case (am, t, e) of
            (A.ValAbbrev, A.Array _ ts, A.ExprLiteral _ _) ->
              -- For "VAL []T a IS [vs]:", we have to use [] rather than * in the
              -- declaration, since you can't say "int *foo = {vs};" in C.
              do tell ["const "]
                 genType ts
                 tell [" "]
                 genName n
                 tell ["[]"]
            _ -> genDecl am t n
          tell [" = "]
          rhs
          tell [";\n"]
          rhsSizes n
introduceSpec (A.Specification _ n (A.IsChannelArray _ t cs))
    =  do genDecl A.Abbrev t n
          tell [" = {"]
          sequence_ $ intersperse genComma (map genVariable cs)
          tell ["};\n"]
--introduceSpec (A.Specification m n (A.DataType m t))
introduceSpec (A.Specification _ n (A.DataTypeRecord _ b fs))
    =  do tell ["typedef struct {\n"]
          sequence_ [case t of
                       _ ->
                         do declareType t
                            tell [" "]
                            genName n
                            tell [";\n"]
                     | (n, t) <- fs]
          tell ["} "]
          when b $ tell ["occam_struct_packed "]
          genName n
          tell [";\n"]
introduceSpec (A.Specification _ n (A.Protocol _ _)) = return ()
introduceSpec (A.Specification _ n (A.ProtocolCase _ ts))
    =  do tell ["typedef enum {\n"]
          sequence_ $ intersperse genComma [genName tag >> tell ["_"] >> genName n
                                            | (tag, _) <- ts]
          tell ["\n"]
          tell ["} "]
          genName n
          tell [";\n"]
introduceSpec (A.Specification _ n (A.Proc _ fs p))
    =  do tell ["void "]
          genName n
          tell [" (Process *me"]
          genFormals fs
          tell [") {\n"]
          genProcess p
          tell ["}\n"]
introduceSpec (A.Specification _ n (A.Function _ _ _ _)) = missing "introduceSpec function"
--introduceSpec (A.Specification _ n (A.Retypes _ am t v))
--introduceSpec (A.Specification _ n (A.RetypesExpr _ am t e))
introduceSpec n = missing $ "introduceSpec " ++ show n

removeSpec :: A.Specification -> CGen ()
removeSpec (A.Specification m n (A.Declaration _ t))
    = case t of
        A.Array _ t' -> overArray var (\sub -> declareFree t' (sub var))
        _ ->
          do case declareFree t var of
               Just p -> p
               Nothing -> return ()
  where
    var = A.Variable m n
removeSpec _ = return ()
--}}}

--{{{  actuals/formals
prefixComma :: [CGen ()] -> CGen ()
prefixComma cs = sequence_ [genComma >> c | c <- cs]

genActuals :: [A.Actual] -> CGen ()
genActuals as = prefixComma (map genActual as)

genActual :: A.Actual -> CGen ()
genActual actual
    = case actual of
        A.ActualExpression t e ->
          case (t, e) of
            (A.Array _ _, A.ExprVariable _ v) ->
              do genVariable v
                 tell [", "]
                 genVariable v
                 tell ["_sizes"]
            _ -> genExpression e
        A.ActualVariable am t v ->
          case t of
            A.Array _ _ ->
              do genVariable v
                 tell [", "]
                 genVariable v
                 tell ["_sizes"]
            _ -> fst $ abbrevVariable am t v

numCArgs :: [A.Actual] -> Int
numCArgs [] = 0
numCArgs (A.ActualVariable _ (A.Array _ _) _:fs) = 2 + numCArgs fs
numCArgs (A.ActualExpression (A.Array _ _) _:fs) = 2 + numCArgs fs
numCArgs (_:fs) = 1 + numCArgs fs

genFormals :: [A.Formal] -> CGen ()
genFormals fs = prefixComma (map genFormal fs)

genFormal :: A.Formal -> CGen ()
genFormal (A.Formal am t n)
    = case t of
        A.Array _ t' ->
          do genDecl am t n
             tell [", const int *"]
             genName n
             tell ["_sizes"]
        _ -> genDecl am t n
--}}}

--{{{  par modes
--}}}

--{{{  processes
genProcess :: A.Process -> CGen ()
genProcess p = case p of
  A.ProcSpec m s p -> genSpec s (genProcess p)
  A.Assign m vs es -> genAssign vs es
  A.Input m c im -> genInput c im
  A.Output m c ois -> genOutput c ois
  A.OutputCase m c t ois -> genOutputCase c t ois
  A.Skip m -> tell ["/* skip */\n"]
  A.Stop m -> genStop m "STOP process"
  A.Main m -> tell ["/* main */\n"]
  A.Seq m ps -> sequence_ $ map genProcess ps
  A.SeqRep m r p -> genReplicator r (genProcess p)
  A.If m s -> genIf m s
  A.Case m e s -> genCase m e s
  A.While m e p -> genWhile e p
  A.Par m pm ps -> genPar pm ps
  A.ParRep m pm r p -> genParRep pm r p
  A.Processor m e p -> missing "PROCESSOR not supported"
  A.Alt m b s -> genAlt b s
  A.ProcCall m n as -> genProcCall n as

--{{{  assignment
genAssign :: [A.Variable] -> A.ExpressionList -> CGen ()
genAssign [v] el
    = case el of
        A.FunctionCallList m n es -> missing "function call"
        A.ExpressionList m [e] ->
          do t <- typeOfVariable v
             doAssign t v e
  where
    doAssign :: A.Type -> A.Variable -> A.Expression -> CGen ()
    doAssign t@(A.Array _ subT) toV (A.ExprVariable m fromV)
        = overArray fromV (\sub -> Just $ doAssign subT (sub toV) (A.ExprVariable m (sub fromV)))
    doAssign t v e
        = case scalarType t of
            Just _ ->
              do genVariable v
                 tell [" = "]
                 genExpression e
                 tell [";\n"]
            Nothing -> missing $ "assignment of type " ++ show t
--}}}
--{{{  input
genInput :: A.Variable -> A.InputMode -> CGen ()
genInput c im
    =  do t <- typeOfVariable c
          case t of
            A.Timer -> case im of 
              A.InputSimple m [A.InVariable m' v] -> genTimerRead c v
              A.InputAfter m e -> genTimerWait e
            _ -> case im of
              A.InputSimple m is -> sequence_ $ map (genInputItem c) is
              A.InputCase m s -> genInputCase m c s
              _ -> missing $ "genInput " ++ show im

genInputCase :: Meta -> A.Variable -> A.Structured -> CGen ()
genInputCase m c s
    =  do t <- typeOfVariable c
          let proto = case t of A.Chan (A.UserProtocol n) -> n
          tag <- makeNonce "case_tag"
          genName proto
          tell [" ", tag, ";\n"]
          tell ["ChanInInt ("]
          genVariable c
          tell [", &", tag, ");\n"]
          tell ["switch (", tag, ") {\n"]
          genInputCaseBody proto c (return ()) s
          tell ["default:\n"]
          genStop m "unhandled variant in CASE input"
          tell ["}\n"]

-- This handles specs in a slightly odd way, because we can't insert specs into
-- the body of a switch.
genInputCaseBody :: A.Name -> A.Variable -> CGen () -> A.Structured -> CGen ()
genInputCaseBody proto c coll (A.Spec _ spec s)
    = genInputCaseBody proto c (genSpec spec coll) s
genInputCaseBody proto c coll (A.OnlyV _ (A.Variant _ n iis p))
    = do tell ["case "]
         genName n
         tell ["_"]
         genName proto
         tell [": {\n"]
         coll
         sequence_ $ map (genInputItem c) iis
         genProcess p
         tell ["break;\n"]
         tell ["}\n"]
genInputCaseBody proto c coll (A.Several _ ss)
    = sequence_ $ map (genInputCaseBody proto c coll) ss

genTimerRead :: A.Variable -> A.Variable -> CGen ()
genTimerRead c v
    =  do tell ["ProcTime (&"]
          genVariable c
          tell [");\n"]
          genVariable v
          tell [" = "]
          genVariable c
          tell [";\n"]

genTimerWait :: A.Expression -> CGen ()
genTimerWait e
    =  do tell ["ProcTimeAfter ("]
          genExpression e
          tell [");\n"]
--}}}
--{{{  output
genOutput :: A.Variable -> [A.OutputItem] -> CGen ()
genOutput c ois = sequence_ $ map (genOutputItem c) ois

genOutputCase :: A.Variable -> A.Name -> [A.OutputItem] -> CGen ()
genOutputCase c tag ois
    =  do t <- typeOfVariable c
          let proto = case t of A.Chan (A.UserProtocol n) -> n
          tell ["ChanOutInt ("]
          genVariable c
          tell [", "]
          genName tag
          tell ["_"]
          genName proto
          tell [");\n"]
          genOutput c ois
--}}}
--{{{  stop
genStop :: Meta -> String -> CGen ()
genStop m s
    =  do tell ["occam_stop ("]
          genMeta m
          tell [", \"", s, "\");\n"]
--}}}
--{{{  if
genIf :: Meta -> A.Structured -> CGen ()
genIf m s
    =  do label <- makeNonce "if_end"
          genIfBody label s
          genStop m "no choice matched in IF process"
          tell [label, ":\n;\n"]

genIfBody :: String -> A.Structured -> CGen ()
genIfBody label s = genStructured s doC
  where
    doC (A.OnlyC m (A.Choice m' e p))
        = do tell ["if ("]
             genExpression e
             tell [") {\n"]
             genProcess p
             tell ["goto ", label, ";\n"]
             tell ["}\n"]
--}}}
--{{{  case
genCase :: Meta -> A.Expression -> A.Structured -> CGen ()
genCase m e s
    =  do tell ["switch ("]
          genExpression e
          tell [") {\n"]
          seenDefault <- genCaseBody (return ()) s
          when (not seenDefault) $
            do tell ["default:\n"]
               genStop m "no option matched in CASE process"
          tell ["}\n"]

-- FIXME -- can this be made common with genInputCaseBody above?
genCaseBody :: CGen () -> A.Structured -> CGen Bool
genCaseBody coll (A.Spec _ spec s)
    = genCaseBody (genSpec spec coll) s
genCaseBody coll (A.OnlyO _ (A.Option _ es p))
    =  do sequence_ [tell ["case "] >> genExpression e >> tell [":\n"] | e <- es]
          tell ["{\n"]
          coll
          genProcess p
          tell ["break;\n"]
          tell ["}\n"]
          return False
genCaseBody coll (A.OnlyO _ (A.Else _ p))
    =  do tell ["default:\n"]
          tell ["{\n"]
          coll
          genProcess p
          tell ["}\n"]
          return True
genCaseBody coll (A.Several _ ss)
    =  do seens <- mapM (genCaseBody coll) ss
          return $ or seens
--}}}
--{{{  while
genWhile :: A.Expression -> A.Process -> CGen ()
genWhile e p
    =  do tell ["while ("]
          genExpression e
          tell [") {\n"]
          genProcess p
          tell ["}\n"]
--}}}
--{{{  par
genPar :: A.ParMode -> [A.Process] -> CGen ()
genPar pm ps
    =  do pids <- mapM (\_ -> makeNonce "pid") ps
          sequence_ $ [do tell ["Process *", pid, " = "]
                          genProcAlloc p
                          tell [";\n"]
                       | (pid, p) <- (zip pids ps)]
          case pm of
            A.PlainPar ->
              do tell ["ProcPar ("]
                 sequence_ $ [tell [pid, ", "] | pid <- pids]
                 tell ["NULL);\n"]
            _ -> missing $ "genPar " ++ show pm
          sequence_ $ [tell ["ProcAllocClean (", pid, ");\n"] | pid <- pids]

genParRep :: A.ParMode -> A.Replicator -> A.Process -> CGen ()
genParRep pm rep p
    =  do pids <- makeNonce "pids"
          index <- makeNonce "i"
          tell ["Process *", pids, "["]
          genReplicatorSize rep
          tell [" + 1];\n"]
          tell ["int ", index, " = 0;\n"]
          genReplicator rep $ do tell [pids, "[", index, "++] = "]
                                 genProcAlloc p
                                 tell [";\n"]
          tell [pids, "[", index, "] = NULL;\n"]
          tell ["ProcParList (", pids, ");\n"]
          tell [index, " = 0;\n"]
          genReplicator rep $ tell ["ProcAllocClean (", pids, "[", index, "++]);\n"]

genProcAlloc :: A.Process -> CGen ()
genProcAlloc (A.ProcCall m n as)
    =  do tell ["ProcAlloc ("]
          genName n
          -- FIXME stack size fixed here
          let stackSize = 65536
          tell [", ", show stackSize, ", ", show $ numCArgs as]
          genActuals as
          tell [")"]
--}}}
--{{{  alt
genAlt :: Bool -> A.Structured -> CGen ()
genAlt isPri s
    =  do tell ["AltStart ();\n"]
          tell ["{\n"]
          genAltEnable s
          tell ["}\n"]
          -- Like occ21, this is always a PRI ALT, so we can use it for both.
          tell ["AltWait ();\n"]
          id <- makeNonce "alt_id"
          tell ["int ", id, " = 0;\n"]
          tell ["{\n"]
          genAltDisable id s
          tell ["}\n"]
          fired <- makeNonce "alt_fired"
          tell ["int ", fired, " = AltEnd ();\n"]
          tell [id, " = 0;\n"]
          label <- makeNonce "alt_end"
          tell ["{\n"]
          genAltProcesses id fired label s
          tell ["}\n"]
          tell [label, ":\n;\n"]

withIf :: A.Expression -> CGen () -> CGen ()
withIf cond body
    =  do tell ["if ("]
          genExpression cond
          tell [") {\n"]
          body
          tell ["}\n"]

genAltEnable :: A.Structured -> CGen ()
genAltEnable s = genStructured s doA
  where
    doA (A.OnlyA _ alt)
        = case alt of
            A.Alternative _ c im _ -> doIn c im
            A.AlternativeCond _ e c im _ -> withIf e $ doIn c im
            A.AlternativeSkip _ e _ -> withIf e $ tell ["AltEnableSkip ();\n"]

    doIn c im
        = do t <- inputType c im
             case t of
               ITTimerRead -> missing "timer read in ALT"
               ITTimerAfter ->
                 do let time = case im of A.InputAfter _ e -> e
                    tell ["AltEnableTimer ("]
                    genExpression time
                    tell [");\n"]
               ITOther ->
                 do tell ["AltEnableChannel ("]
                    genVariable c
                    tell [");\n"]

genAltDisable :: String -> A.Structured -> CGen ()
genAltDisable id s = genStructured s doA
  where
    doA (A.OnlyA _ alt)
        = case alt of
            A.Alternative _ c im _ -> doIn c im
            A.AlternativeCond _ e c im _ -> withIf e $ doIn c im
            A.AlternativeSkip _ e _ -> withIf e $ tell ["AltDisableSkip (", id, "++);\n"]

    doIn c im
        = do t <- inputType c im
             case t of
               ITTimerRead -> missing "timer read in ALT"
               ITTimerAfter ->
                 do let time = case im of A.InputAfter _ e -> e
                    tell ["AltDisableTimer (", id, "++, "]
                    genExpression time
                    tell [");\n"]
               ITOther ->
                 do tell ["AltDisableChannel (", id, "++, "]
                    genVariable c
                    tell [");\n"]

genAltProcesses :: String -> String -> String -> A.Structured -> CGen ()
genAltProcesses id fired label s = genStructured s doA
  where
    doA (A.OnlyA _ alt)
        = case alt of
            A.Alternative _ c im p -> doIn c im p
            A.AlternativeCond _ e c im p -> withIf e $ doIn c im p
            A.AlternativeSkip _ e p -> withIf e $ doCheck (genProcess p)

    doIn c im p
        = do t <- inputType c im
             case t of
               ITTimerRead -> missing "timer read in ALT"
               ITTimerAfter -> doCheck (genProcess p)
               ITOther -> doCheck (genInput c im >> genProcess p)

    doCheck body
        = do tell ["if (", id, "++ == ", fired, ") {\n"]
             body
             tell ["goto ", label, ";\n"]
             tell ["}\n"]
--}}}
--{{{  proc call
genProcCall :: A.Name -> [A.Actual] -> CGen ()
genProcCall n as
    =  do genName n
          tell [" (me"]
          genActuals as
          tell [");\n"]
--}}}
--}}}

