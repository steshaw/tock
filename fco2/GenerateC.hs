-- | Generate C code from the mangled AST.
module GenerateC where

-- FIXME: Use Structured for Par and Seq (and ValOf, etc.). This would make it
-- easier to put {} around sets of declarations.

-- FIXME: Checks should be done in the parser, not here -- for example, the
-- expressionList production should take an argument with a list of types.

-- FIXME: The show instance for types should produce occam-looking types.

-- FIXME: Should have a "current type context" in the parser, so that
-- VAL BYTE b IS 4: works correctly.

-- FIXME: Tock would be a good name for this (Translator from occam to C from Kent).

-- FIXME: Should have a pass that converts functions to procs, and calls to a
-- call outside the enclosing process (which can be found by a generic pass
-- over the tree).
-- And array subscripts also.

-- FIXME: There should be a wrapper for SetErr that takes a Meta and an error
-- message. Ops and array references should use it.

-- FIXME: We could have genSpec generate {} around specs if it's not
-- immediately inside another spec (which'd require some extra boolean
-- arguments to find out).

-- FIXME: If the assembler-analysis approach to working out process sizes
-- works, then we can put the sizes in variables in a separate object file and
-- only generate/compile that after we've done the main one.

-- FIXME: Before code generation, have a pass that resolves all the DATA TYPE
-- .. IS directives to their real types.

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
import Errors
import Types

--{{{  monad definition
type CGen a = WriterT [String] (ErrorT String (StateT ParseState IO)) a
--}}}

--{{{  top-level
generateC :: ParseState -> A.Process -> IO String
generateC st ast
    =  do v <- evalStateT (runErrorT (runWriterT (genTopLevel ast))) st
          case v of
            Left e -> die e
            Right (_, ss) -> return $ concat ss

genTopLevel :: A.Process -> CGen ()
genTopLevel p
    =  do tell ["#include <fco_support.h>\n"]
          genProcess p

          ps <- get
          let mainName = fromJust $ psMainName ps
          tell ["void fco_main (Process *me, Channel *in, Channel *out, Channel *err) {\n"]
          genName mainName
          -- FIXME This should depend on what interface it's actually got.
          tell [" (me, in, out, err);\n"]
          tell ["}\n"]
--}}}

--{{{  utilities
missing :: String -> CGen ()
missing s = tell ["\n#error Unimplemented: ", s, "\n"]

genComma :: CGen ()
genComma = tell [", "]

withPS :: (ParseState -> a) -> CGen a
withPS f
    =  do st <- get
          return $ f st

checkJust :: Monad m => Maybe t -> m t
checkJust (Just v) = return v
checkJust Nothing = fail "checkJust failed"

overArray :: CGen () -> A.Type -> (CGen () -> Maybe (CGen ())) -> CGen ()
overArray name (A.Array ds _) func
    =  do indices <- mapM (\_ -> makeNonce "i") ds
          let arg = sequence_ [tell ["[", i, "]"] | i <- indices]
          case func arg of
            Just p ->
              do sequence_ [do tell ["for (int ", i, " = 0; ", i, " < "]
                               name
                               tell ["_sizes[", show v, "]; ", i, "++) {\n"]
                            | (v, i) <- zip [0..] indices]
                 p
                 sequence_ [tell ["}\n"] | i <- indices]
            Nothing -> return ()
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
    genBytesInDims ((A.Dimension e):ds)
        = genBytesInDims ds >> genExpression e >> tell [" * "]
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
genConversion :: A.ConversionMode -> A.Type -> A.Expression -> CGen ()
genConversion A.DefaultConversion t e
    =  do tell ["(("]
          genType t
          tell [") "]
          genExpression e
          tell [")"]
genConversion cm t e = missing $ "genConversion " ++ show cm
--}}}

--{{{  literals
genLiteral :: A.Literal -> CGen ()
genLiteral (A.Literal m t lr) = genLiteralRepr lr
genLiteral l = missing $ "genLiteral " ++ show l

genLiteralRepr :: A.LiteralRepr -> CGen ()
genLiteralRepr (A.RealLiteral m s) = tell [s]
genLiteralRepr (A.IntLiteral m s) = tell [s]
genLiteralRepr (A.HexLiteral m s) = case s of ('#':rest) -> tell ["0x", rest]
genLiteralRepr (A.ByteLiteral m s) = tell ["'", convStringLiteral s, "'"]
genLiteralRepr (A.StringLiteral m s) = tell ["\"", convStringLiteral s, "\""]
genLiteralRepr (A.ArrayLiteral m es)
    =  do tell ["{"]
          sequence_ $ intersperse genComma (map genExpression es)
          tell ["}"]

hexToOct :: String -> String
hexToOct h = printf "%03o" (fst $ head $ readHex h)

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
    =  do ps <- get
          am <- checkJust $ abbrevModeOfVariable ps v
          t <- checkJust $ typeOfVariable ps v
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
              ps <- get
              t <- checkJust $ typeOfVariable ps v
              let numDims = case t of A.Array ds _ -> length ds
              genVariable v
              tell ["["]
              sequence_ $ intersperse (tell [" + "]) $ genPlainSub v es [0..(numDims - 1)]
              tell ["]"]
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

    -- | Generate the individual offsets that need adding together to find the
    -- right place in the array.
    -- FIXME This is obviously not the best way to factor this, but I figure a
    -- smart C compiler should be able to work it out...
    genPlainSub :: A.Variable -> [A.Expression] -> [Int] -> [CGen ()]
    genPlainSub _ [] _ = []
    genPlainSub v (e:es) (_:subs)
        = gen : genPlainSub v es subs
      where
        gen = sequence_ $ intersperse (tell [" * "]) $ genExpression e : genChunks
        genChunks = [genVariable v >> tell ["_sizes[", show i, "]"] | i <- subs]
--}}}

--{{{  expressions
genExpression :: A.Expression -> CGen ()
genExpression (A.Monadic m op e) = genMonadic op e
genExpression (A.Dyadic m op e f) = genDyadic op e f
genExpression (A.MostPos m t) = genTypeConstant "mostpos" t
genExpression (A.MostNeg m t) = genTypeConstant "mostneg" t
--genExpression (A.SizeType m t)
genExpression (A.SizeExpr m e)
    =  do genExpression e
          tell ["_sizes[0]"]
genExpression (A.SizeVariable m v)
    =  do genVariable v
          tell ["_sizes[0]"]
genExpression (A.Conversion m cm t e) = genConversion cm t e
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

genTypeConstant :: String -> A.Type -> CGen ()
genTypeConstant s t
    = case scalarType t of
        Just ct -> tell ["occam_", s, "_", ct]
        Nothing -> missing $ "genTypeConstant " ++ show t
--}}}

--{{{  operators
genSimpleMonadic :: String -> A.Expression -> CGen ()
genSimpleMonadic s e
    =  do tell ["(", s]
          genExpression e
          tell [")"]

genMonadic :: A.MonadicOp -> A.Expression -> CGen ()
genMonadic A.MonadicSubtr e = genSimpleMonadic "-" e
genMonadic A.MonadicBitNot e = genSimpleMonadic "~" e
genMonadic A.MonadicNot e = genSimpleMonadic "!" e

genSimpleDyadic :: String -> A.Expression -> A.Expression -> CGen ()
genSimpleDyadic s e f
    =  do tell ["("]
          genExpression e
          tell [" ", s, " "]
          genExpression f
          tell [")"]

genFuncDyadic :: String -> A.Expression -> A.Expression -> CGen ()
genFuncDyadic s e f
    =  do tell [s, " ("]
          genExpression e
          tell [", "]
          genExpression f
          tell [")"]

genDyadic :: A.DyadicOp -> A.Expression -> A.Expression -> CGen ()
genDyadic A.Add e f = genFuncDyadic "occam_add" e f
genDyadic A.Subtr e f = genFuncDyadic "occam_subtr" e f
genDyadic A.Mul e f = genFuncDyadic "occam_mul" e f
genDyadic A.Div e f = genFuncDyadic "occam_div" e f
genDyadic A.Rem e f = genFuncDyadic "occam_rem" e f
genDyadic A.Plus e f = genSimpleDyadic "+" e f
genDyadic A.Minus e f = genSimpleDyadic "-" e f
genDyadic A.Times e f = genSimpleDyadic "*" e f
genDyadic A.BitAnd e f = genSimpleDyadic "&" e f
genDyadic A.BitOr e f = genSimpleDyadic "|" e f
genDyadic A.BitXor e f = genSimpleDyadic "^" e f
genDyadic A.And e f = genSimpleDyadic "&&" e f
genDyadic A.Or e f = genSimpleDyadic "||" e f
genDyadic A.Eq e f = genSimpleDyadic "==" e f
genDyadic A.NotEq e f = genSimpleDyadic "!=" e f
genDyadic A.Less e f = genSimpleDyadic "<" e f
genDyadic A.More e f = genSimpleDyadic ">" e f
genDyadic A.LessEq e f = genSimpleDyadic "<=" e f
genDyadic A.MoreEq e f = genSimpleDyadic ">=" e f
genDyadic A.After e f = genFuncDyadic "occam_after" e f
--}}}

--{{{  input/output items
genInputItem :: A.Variable -> A.InputItem -> CGen ()
genInputItem c (A.InCounted m cv av)
    =  do genInputItem c (A.InVariable m cv)
          ps <- get
          t <- checkJust $ typeOfVariable ps av
          tell ["ChanIn ("]
          genVariable c
          tell [", "]
          fst $ abbrevVariable A.Abbrev t av
          tell [", "]
          let subT = fromJust $ subscriptType ps (A.Subscript m $ makeConstant m 0) t
          genVariable cv
          tell [" * "]
          genBytesInType subT
          tell [");\n"]
genInputItem c (A.InVariable m v)
    =  do ps <- get
          t <- checkJust $ typeOfVariable ps v
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
          ps <- get
          t <- checkJust $ typeOfExpression ps ae
          case ae of
            A.ExprVariable m v ->
              do tell ["ChanOut ("]
                 genVariable c
                 tell [", "]
                 fst $ abbrevVariable A.Abbrev t v
                 tell [", "]
                 let subT = fromJust $ subscriptType ps (A.Subscript m $ makeConstant m 0) t
                 genExpression ce
                 tell [" * "]
                 genBytesInType subT
                 tell [");\n"]
genOutputItem c (A.OutExpression m e)
    =  do ps <- get
          t <- checkJust $ typeOfExpression ps e
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
            -- FIXME It would be cleaner to do this with a pullup,
            -- which would reduce it to the previous case.
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

-- FIXME This should be special-cased for when base == 0 to generate the sort
-- of loop a C programmer would normally write.
genReplicatorLoop :: A.Replicator -> CGen ()
genReplicatorLoop (A.For m n base count)
    =  do counter <- makeNonce "replicator_count"
          tell ["int ", counter, " = "]
          genExpression count
          tell [", "]
          genName n
          tell [" = "]
          genExpression base
          tell ["; ", counter, " > 0; ", counter, "--, "]
          genName n
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
                    (do genExpression count
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
        = genArraySize False $ sequence_ $ intersperse genComma [genExpression e | A.Dimension e <- ds]
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
                                 [case d of A.Dimension e -> genExpression e | d <- ds]
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
          sequence_ $ intersperse genComma [genExpression e | (A.Dimension e) <- ds]
          tell [" };\n"]

-- | Initialise an item being declared.
declareInit :: A.Type -> CGen () -> CGen () -> Maybe (CGen ())
declareInit (A.Chan _) name index
    = Just $ do tell ["ChanInit (&"]
                name
                index
                tell [");\n"]
declareInit t@(A.Array ds t') name _    -- index ignored because arrays can't nest
    = Just $ do init <- case t' of
                          A.Chan _ ->
                            do store <- makeNonce "storage"
                               tell ["Channel ", store]
                               genDimensions ds
                               tell [";\n"]
                               return (\index -> Just $ do fromJust $ declareInit t' (tell [store]) index
                                                           name
                                                           index
                                                           tell [" = &", store]
                                                           index
                                                           tell [";\n"])
                          _ -> return $ declareInit t' name
                overArray name t init
declareInit _ _ _ = Nothing

-- | Free a declared item that's going out of scope.
declareFree :: A.Type -> CGen () -> CGen () -> Maybe (CGen ())
declareFree _ _ _ = Nothing

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
introduceSpec (A.Specification _ n (A.Declaration _ t))
    = do genDeclaration t n
         case t of
           A.Array ds _ -> declareArraySizes ds (genName n)
           _ -> return ()
         case declareInit t (genName n) (return ()) of
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
          genDecl am t n
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
removeSpec (A.Specification _ n (A.Declaration _ t))
    = case t of
        A.Array _ t' -> overArray (genName n) t (declareFree t' (genName n))
        _ ->
          do case declareFree t (genName n) (return ()) of
               Just p -> p
               Nothing -> return ()
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
  A.Stop m -> genStop
  A.Main m -> tell ["/* main */\n"]
  A.Seq m ps -> sequence_ $ map genProcess ps
  A.SeqRep m r p -> genReplicator r (genProcess p)
  A.If m s -> genIf s
  A.Case m e s -> genCase e s
  A.While m e p -> genWhile e p
  A.Par m pm ps -> genPar pm ps
  A.ParRep m pm r p -> genParRep pm r p
  A.Processor m e p -> missing "PROCESSOR not supported"
  A.Alt m b s -> genAlt b s
  A.ProcCall m n as -> genProcCall n as

--{{{  assignment
genAssign :: [A.Variable] -> A.ExpressionList -> CGen ()
genAssign vs el
    = case el of
        A.FunctionCallList m n es -> missing "function call"
        A.ExpressionList m es -> case vs of
          [v] ->
            do genVariable v
               tell [" = "]
               genExpression (head es)
               tell [";\n"]
          vs ->
            do tell ["{\n"]
               ns <- mapM (\_ -> makeNonce "assign_tmp") vs
               mapM (\(v, n, e) -> do st <- get
                                      t <- checkJust $ typeOfVariable st v
                                      genType t
                                      tell [" ", n, " = "]
                                      genExpression e
                                      tell [";\n"])
                    (zip3 vs ns es)
               mapM (\(v, n) -> do genVariable v
                                   tell [" = ", n, ";\n"])
                    (zip vs ns)
               tell ["}\n"]
--}}}
--{{{  input
genInput :: A.Variable -> A.InputMode -> CGen ()
genInput c im
    =  do ps <- get
          t <- checkJust $ typeOfVariable ps c
          case t of
            A.Timer -> case im of 
              A.InputSimple m [A.InVariable m' v] -> genTimerRead c v
              A.InputAfter m e -> genTimerWait e
            _ -> case im of
              A.InputSimple m is -> sequence_ $ map (genInputItem c) is
              A.InputCase m s -> genInputCase c s
              _ -> missing $ "genInput " ++ show im

genInputCase :: A.Variable -> A.Structured -> CGen ()
genInputCase c s
    =  do ps <- get
          t <- checkJust $ typeOfVariable ps c
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
          genStop
          tell ["}\n"]

-- This handles specs in a slightly odd way, because we can't insert specs into
-- the body of a switch.
genInputCaseBody :: A.Name -> A.Variable -> CGen () -> A.Structured -> CGen ()
genInputCaseBody proto c coll (A.Spec _ spec s)
    = genInputCaseBody proto c (genSpec spec coll) s
genInputCaseBody proto c coll (A.OnlyV _ (A.Variant _ n iis p))
    =  do tell ["case "]
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
    =  do ps <- get
          t <- checkJust $ typeOfVariable ps c
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
genStop :: CGen ()
genStop = tell ["SetErr ();\n"]
--}}}
--{{{  if
-- FIXME: This could be special-cased to generate if ... else if ... for bits
-- that aren't replicated and don't have specs.
-- FIXME: As with CASE, this could use a flag to detect whether to generate the STOP.
genIf :: A.Structured -> CGen ()
genIf s
    =  do label <- makeNonce "if_end"
          genIfBody label s
          genStop
          tell [label, ":\n;\n"]

genIfBody :: String -> A.Structured -> CGen ()
genIfBody label (A.Rep m rep s) = genReplicator rep (genIfBody label s)
genIfBody label (A.Spec m spec s) = genSpec spec (genIfBody label s)
genIfBody label (A.OnlyC m (A.Choice m' e p))
    =  do tell ["if ("]
          genExpression e
          tell [") {\n"]
          genProcess p
          tell ["goto ", label, ";\n"]
          tell ["}\n"]
genIfBody label (A.Several m ss) = sequence_ $ map (genIfBody label) ss
--}}}
--{{{  case
genCase :: A.Expression -> A.Structured -> CGen ()
genCase e s
    =  do tell ["switch ("]
          genExpression e
          tell [") {\n"]
          seenDefault <- genCaseBody (return ()) s
          when (not seenDefault) $ tell ["default:\n"] >> genStop
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

-- FIXME -- This'll require a C99 dynamic array for a dynamic PAR count,
-- which may turn out to be a bad idea for very large counts (since I assume
-- it'll allocate off the stack). We should probably do a malloc if it's
-- not determinable at compile time.
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
          let stackSize = 4096
          tell [", ", show stackSize, ", ", show $ numCArgs as]
          genActuals as
          tell [")"]
--}}}
--{{{  alt
-- FIXME This will always generate a dynamic array -- we'd need a pass to tell
-- if all the replicator sizes were constant.
-- The code it generates is really not very nice; it would be better if CIF
-- exposed the enable/wait/disable instructions.
genAlt :: Bool -> A.Structured -> CGen ()
genAlt isPri s
    =  do chans <- makeNonce "channels"
          count <- makeNonce "count"
          tell ["int ", count, " = 1;\n"]
          tell ["{\n"]
          genAltSize count s
          tell ["}\n"]
          tell ["Channel *", chans, "[", count, "];\n"]
          tell [count, " = 0;\n"]
          tell ["{\n"]
          genAltEnable chans count s
          tell ["}\n"]
          tell [chans, "[", count, "] = NULL;\n"]
          fired <- makeNonce "fired"
          label <- makeNonce "end"
          tell ["int ", fired, " = "]
          tell [if isPri then "ProcProcPriAltList" else "ProcAltList"]
          tell [" (", chans, ");\n"]
          tell [count, " = 0;\n"]
          tell ["{\n"]
          genAltDisable fired count label s
          tell ["}\n"]
          tell [label, ":\n;\n"]

genAltSize :: String -> A.Structured -> CGen ()
genAltSize count (A.Rep _ rep s) = genReplicator rep (genAltSize count s)
genAltSize count (A.Spec _ spec s) = genSpec spec (genAltSize count s)
genAltSize count (A.OnlyA _ alt)
    = case alt of
        A.Alternative _ _ _ _ -> tell [count, "++;\n"]
        A.AlternativeCond _ _ _ _ _ -> tell [count, "++;\n"]
        A.AlternativeSkip _ _ _ -> return ()
genAltSize count (A.Several _ ss) = sequence_ $ map (genAltSize count) ss

genAltEnable :: String -> String -> A.Structured -> CGen ()
genAltEnable chans count (A.Rep _ rep s) = genReplicator rep (genAltEnable chans count s)
genAltEnable chans count (A.Spec _ spec s) = genSpec spec (genAltEnable chans count s)
genAltEnable chans count (A.OnlyA _ alt)
    = case alt of
        A.Alternative _ c _ _ ->
          do tell [chans, "[", count, "++] = "]
             genVariable c
             tell [";\n"]
        A.AlternativeCond _ e c _ _ ->
          do tell ["if ("]
             genExpression e
             tell [") {\n"]
             tell [chans, "[", count, "++] = "]
             genVariable c
             tell [";\n"]
             tell ["}\n"]
        A.AlternativeSkip _ _ _ -> return ()
genAltEnable chans count (A.Several _ ss) = sequence_ $ map (genAltEnable chans count) ss

genAltDisable :: String -> String -> String -> A.Structured -> CGen ()
genAltDisable fired count label (A.Rep _ rep s) = genReplicator rep (genAltDisable fired count label s)
genAltDisable fired count label (A.Spec _ spec s) = genSpec spec (genAltDisable fired count label s)
genAltDisable fired count label (A.OnlyA _ alt)
    = case alt of
        A.Alternative _ c im p ->
          do tell ["if (", fired, " == ", count, "++) {\n"]
             genInput c im
             genProcess p
             tell ["goto ", label, ";\n"]
             tell ["}\n"]
        A.AlternativeCond _ e c im p ->
          do tell ["if (("]
             genExpression e
             tell [") && ", fired, " == ", count, "++) {\n"]
             genInput c im
             genProcess p
             tell ["goto ", label, ";\n"]
             tell ["}\n"]
        -- FIXME This doesn't do anything useful yet, since CIF doesn't do SKIP guards.
        A.AlternativeSkip _ e p ->
          do tell ["if (("]
             genExpression e
             tell [") && ", fired, " == -1) {\n"]
             genProcess p
             tell ["goto ", label, ";\n"]
             tell ["}\n"]
             missing "SKIP guards not supported"
genAltDisable fired count label (A.Several _ ss) = sequence_ $ map (genAltDisable fired count label) ss
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

