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
-- Array constants need pulling up at the same time (might as well avoid
-- walking the tree twice!).
-- And slices. Subscripts generally?

-- FIXME: The timer read mess can be cleaned up -- when you declare a timer,
-- that declares the temp variable...

-- FIXME: There should be a wrapper for SetErr that takes a Meta and an error
-- message. Ops and array references should use it.

import Data.List
import Data.Maybe
import Control.Monad.Writer
import Control.Monad.Error
import Control.Monad.State

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

checkJust :: Maybe t -> CGen t
checkJust (Just v) = return v
checkJust Nothing = fail "checkJust failed"

overArray :: A.Name -> A.Type -> (CGen () -> Maybe (CGen ())) -> CGen ()
overArray n (A.Array ds _) func
    =  do indices <- mapM (\_ -> makeNonce "i") ds
          let arg = sequence_ [tell ["[", i, "]"] | i <- indices]
          case func arg of
            Just p ->
              do sequence_ [do tell ["for (int ", i, " = 0; ", i, " < "]
                               genName n
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
scalarType _ = Nothing

genType :: A.Type -> CGen ()
genType (A.Array _ t)
    =  do genType t
          tell ["*"]
genType (A.UserDataType n) = genName n
genType (A.Chan t) = tell ["Channel *"]
genType t
    = case scalarType t of
        Just s -> tell [s]
        Nothing -> missing $ "genType " ++ show t
--}}}

--{{{  declarations
genDeclType :: A.AbbrevMode -> A.Type -> CGen ()
genDeclType am t
    =  do when (am == A.ValAbbrev) $ tell ["const "]
          genType t
          case t of
            A.Array _ _ -> return ()
            A.Chan _ -> return ()
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

--{{{  subscripts
genSubscript :: A.Subscript -> CGen () -> CGen ()
genSubscript (A.Subscript m e) p
    =  do p
          tell ["["]
          genExpression e
          tell ["]"]
genSubscript (A.SubscriptTag m n) p
    =  do p
          tell ["."]
          genName n
genSubscript s p = missing $ "genSubscript " ++ show s
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

convStringLiteral :: String -> String
convStringLiteral [] = []
convStringLiteral ('*':'#':a:b:s) = "\\x" ++ [a, b] ++ convStringLiteral s
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
                                  Original      Abbrev
                                  ValAbbrev

INT x:                x           x             *x         int x;          int *x;
[10]INT xs:           xs[i]       xs[i]         xs[i]      int xs[10];     int *xs;
                      xs          xs            xs

                                  Original      Abbrev

CHAN OF INT c:        c           &c            c          Channel c;       Channel *c;
[10]CHAN OF INT cs:   cs[i]       cs[i]         cs[i]      Channel *cs[10]; Channel **cs;
                      cs          cs            cs

[2][2]INT xss:        xss[i][j]   xss[i][j]     xss[i][j]
                      xss         xss           xss
[2][2]CHAN INT css:   css[i][j]   css[i][j]     css[i][j]
                      css         css           css

I suspect there's probably a nicer way of doing this, but as a translation of
the above table this isn't too horrible...
-}
genVariable :: A.Variable -> CGen ()
genVariable v
    =  do ps <- get
          am <- checkJust $ abbrevModeOfVariable ps v
          t <- checkJust $ typeOfVariable ps v

          let isArray = case t of
                          A.Array _ _ -> True
                          _ -> False
          let isSubbed = case v of
                           A.SubscriptedVariable _ _ _ -> True
                           _ -> False
          let isChan = case stripArrayType t of
                         A.Chan _ -> True
                         _ -> False

          when ((am == A.Abbrev) && (not (isChan || isArray || isSubbed))) $
               tell ["*"]

          when ((am == A.Original) && isChan && not (isArray || isSubbed)) $
               tell ["&"]

          inner v
  where
    inner (A.Variable m n) = genName n
    inner (A.SubscriptedVariable m s v) = genSubscript s (inner v)
--}}}

--{{{  expressions
genExpression :: A.Expression -> CGen ()
genExpression (A.Monadic m op e) = genMonadic op e
genExpression (A.Dyadic m op e f) = genDyadic op e f
genExpression (A.MostPos m t) = genTypeConstant "mostpos" t
genExpression (A.MostNeg m t) = genTypeConstant "mostneg" t
--genExpression (A.Size m t)
genExpression (A.Conversion m cm t e) = genConversion cm t e
genExpression (A.ExprVariable m v) = genVariable v
genExpression (A.ExprLiteral m l) = genLiteral l
genExpression (A.True m) = tell ["true"]
genExpression (A.False m) = tell ["false"]
--genExpression (A.FunctionCall m n es)
--genExpression (A.SubscriptedExpr m s e)
--genExpression (A.BytesInExpr m e)
-- FIXME This needs to do special stuff with arrays.
genExpression (A.BytesInType m t)
    =  do tell ["sizeof ("]
          genType t
          tell [")"]
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
-- FIXME This needs to cope with subscripts
genMonadic A.MonadicSize e
    =  do genExpression e
          tell ["_sizes[0]"]

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
          -- need to then input as much as appropriate
          missing "genInputItem counted"
genInputItem c (A.InVariable m v)
    =  do ps <- get
          t <- checkJust $ typeOfVariable ps v
          case t of
            A.Int ->
              do tell ["ChanInInt ("]
                 genVariable c
                 tell [", &"]
                 genVariable v
                 tell [");\n"]
            _ ->
              do tell ["ChanIn ("]
                 genVariable c
                 tell [", &"]
                 genVariable v
                 tell [", sizeof ("]
                 genType t
                 tell ["));\n"]

genOutputItem :: A.Variable -> A.OutputItem -> CGen ()
genOutputItem c (A.OutCounted m ce ae)
    =  do genOutputItem c (A.OutExpression m ce)
          missing "genOutputItem counted"
genOutputItem c (A.OutExpression m e)
    =  do n <- makeNonce "output_item"
          ps <- get
          t <- checkJust $ typeOfExpression ps e
          case t of
            A.Int ->
              do tell ["ChanOutInt ("]
                 genVariable c
                 tell [", "]
                 genExpression e
                 tell [");\n"]
            _ ->
              do tell ["{\n"]
                 tell ["const "]
                 genType t
                 tell [" ", n, " = "]
                 genExpression e
                 tell [";\n"]
                 tell ["ChanOut ("]
                 genVariable c
                 tell [", &", n, ", sizeof ("]
                 genType t
                 tell ["));\n"]
                 tell ["}\n"]
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
--}}}

--{{{  choice/alternatives/options/variants
--}}}

--{{{  structured
--}}}

--{{{  abbreviations
-- | Generate the right-hand side of an abbreviation of a variable.
abbrevVariable :: A.AbbrevMode -> A.Type -> A.Variable -> (CGen (), Maybe (CGen ()))
abbrevVariable am (A.Array _ _) v
    = (genVariable v, Just $ do { genVariable v; tell ["_sizes"] })
abbrevVariable am (A.Chan _) v
    = (genVariable v, Nothing)
abbrevVariable am t v
    = (do { when (am == A.Abbrev) $ tell ["&"]; genVariable v }, Nothing)

-- | Generate the right-hand side of an abbreviation of an expression.
abbrevExpression :: A.AbbrevMode -> A.Type -> A.Expression -> (CGen (), Maybe (CGen ()))
abbrevExpression am t@(A.Array _ _) e
    = case e of
        A.ExprVariable _ v -> abbrevVariable am t v
        A.ExprLiteral _ l ->
          case l of
            A.Literal _ litT r -> (genExpression e, Just $ genTypeSize litT)
            A.SubscriptedLiteral _ _ _ -> bad
        _ -> bad
  where
    bad = (missing "array expression abbreviation", Just $ missing "AEA size")

    genTypeSize :: A.Type -> CGen ()
    genTypeSize (A.Array ds _)
        =  do tell ["{ "]
              sequence_ $ intersperse genComma [genExpression e | A.Dimension e <- ds]
              tell [" }"]
abbrevExpression am _ e
    = (genExpression e, Nothing)
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

-- | Initialise an item being declared.
declareInit :: A.Type -> CGen () -> CGen () -> Maybe (CGen ())
declareInit (A.Chan _) name index
    = Just $ do tell ["ChanInit (&"]
                name
                index
                tell [");\n"]
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
                          const int ds_sizes[] = cs_sizes;
-}
introduceSpec :: A.Specification -> CGen ()
introduceSpec (n, A.Declaration m t)
    = case t of
        A.Timer -> return ()
        A.Chan _ ->
          do tell ["Channel "]
             genName n
             tell [";\n"]
             tell ["ChanInit (&"]
             genName n
             tell [");\n"]
        A.Array ds t' ->
          do declareType t'
             tell [" "]
             genName n
             let dim = sequence_ $ [case d of
                                      A.Dimension e ->
                                        do tell ["["]
                                           genExpression e
                                           tell ["]"]
                                      A.UnknownDimension ->
                                        missing "unknown dimension in declaration"
                                    | d <- ds]
             dim
             tell [";\n"]
             init <- case t' of
                       A.Chan _ ->
                         do store <- makeNonce "storage"
                            tell ["Channel ", store]
                            dim
                            tell [";\n"]
                            return (\index -> Just $ do fromJust $ declareInit t' (tell [store]) index
                                                        genName n
                                                        index
                                                        tell [" = &", store]
                                                        index
                                                        tell [";\n"])
                       _ -> return $ declareInit t' (genName n)
             tell ["const int "]
             genName n
             tell ["_sizes[] = { "]
             sequence_ $ intersperse genComma [genExpression e | (A.Dimension e) <- ds]
             tell [" };\n"]
             overArray n t init
        _ ->
          do declareType t
             tell [" "]
             genName n
             tell [";\n"]
             case declareInit t (genName n) (return ()) of
               Just p -> p
               Nothing -> return ()
introduceSpec (n, A.Is m am t v)
    =  do let (rhs, rhsSizes) = abbrevVariable am t v
          genDecl am t n
          tell [" = "]
          rhs
          tell [";\n"]
          case rhsSizes of
            Just r ->
              do tell ["const int "]
                 genName n
                 tell ["_sizes[] = "]
                 r
                 tell [";\n"]
            Nothing -> return ()
introduceSpec (n, A.IsExpr m am t e)
    =  do let (rhs, rhsSizes) = abbrevExpression am t e
          genDecl am t n
          tell [" = "]
          rhs
          tell [";\n"]
          case rhsSizes of
            Just r ->
              do tell ["const int "]
                 genName n
                 tell ["_sizes[] = "]
                 r
                 tell [";\n"]
            Nothing -> return ()
introduceSpec (n, A.IsChannelArray m t cs)
    =  do genDecl A.Abbrev t n
          tell [" = {"]
          sequence_ $ intersperse genComma (map genVariable cs)
          tell ["};\n"]
introduceSpec (n, A.Proc m fs p)
    =  do tell ["void "]
          genName n
          tell [" ("]
          genFormals fs
          tell [") {\n"]
          genProcess p
          tell ["}\n"]
-- CASE protocol should generate an enum for the tags
introduceSpec (n, t) = missing $ "introduceSpec " ++ show t

removeSpec :: A.Specification -> CGen ()
removeSpec (n, A.Declaration m t)
    = case t of
        A.Array _ t' -> overArray n t (declareFree t' (genName n))
        _ ->
          do case declareFree t (genName n) (return ()) of
               Just p -> p
               Nothing -> return ()
removeSpec _ = return ()
--}}}

--{{{  actuals/formals
genActuals :: [(A.Actual, A.Formal)] -> CGen ()
genActuals afs = sequence_ $ intersperse genComma (map genActual afs)

genActual :: (A.Actual, A.Formal) -> CGen ()
genActual (actual, A.Formal am t _)
    = case actual of
        A.ActualExpression e ->
          do let (rhs, rhsSizes) = abbrevExpression am t e
             rhs
             case rhsSizes of
               Just r ->
                 do tell [", "]
                    r
               Nothing -> return ()
        A.ActualVariable v ->
          do let (rhs, rhsSizes) = abbrevVariable am t v
             rhs
             case rhsSizes of
               Just r ->
                 do tell [", "]
                    r
               Nothing -> return ()

genFormals :: [A.Formal] -> CGen ()
genFormals fs = sequence_ $ intersperse genComma (map genFormal fs)

genFormal :: A.Formal -> CGen ()
genFormal (A.Formal am t n)
    = case t of
        (A.Array _ t) ->
          do genDecl am t n
             tell ["[], const int "]
             genName n
             tell ["_sizes[]"]
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
  --A.OutputCase m c t ois
  A.Skip m -> tell ["/* skip */\n"]
  A.Stop m -> genStop
  A.Main m -> tell ["/* main */\n"]
  A.Seq m ps -> sequence_ $ map genProcess ps
  A.SeqRep m r p -> genReplicator r (genProcess p)
  A.If m s -> genIf s
  --A.Case m e s
  A.While m e p -> genWhile e p
  A.Par m pm ps -> genPar pm ps
  --A.ParRep m pm r p
  --A.Processor m e p
  --A.Alt m b s
  A.ProcCall m n as -> genProcCall n as
  _ -> missing $ "genProcess " ++ show p

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

genInput :: A.Variable -> A.InputMode -> CGen ()
genInput c im
    =  do ps <- get
          t <- checkJust $ typeOfVariable ps c
          case t of
            A.Timer -> case im of 
              A.InputSimple m [A.InVariable m' v] -> genTimerRead v
              A.InputAfter m e -> genTimerWait e
            _ -> case im of
              A.InputSimple m is -> sequence_ $ map (genInputItem c) is
              _ -> missing $ "genInput " ++ show im

genTimerRead :: A.Variable -> CGen ()
genTimerRead v
    =  do n <- makeNonce "time"
          tell ["{\n"]
          tell ["Time ", n, ";\n"]
          tell ["ProcTime (&", n, ");\n"]
          genVariable v
          tell [" = ", n, ";\n"]
          tell ["}\n"]

genTimerWait :: A.Expression -> CGen ()
genTimerWait e
    =  do tell ["ProcTimeAfter ("]
          genExpression e
          tell [");\n"]

genOutput :: A.Variable -> [A.OutputItem] -> CGen ()
genOutput c ois = sequence_ $ map (genOutputItem c) ois

genStop :: CGen ()
genStop = tell ["SetErr ();\n"]

-- FIXME: This could be special-cased to generate if ... else if ... for bits
-- that aren't replicated and don't have specs.
genIf :: A.Structured -> CGen ()
genIf s
    =  do label <- makeNonce "if_end"
          genIfBody label s
          genStop
          tell [label, ":\n;\n"]

-- FIXME: This should be generic for any Structured type.
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

genWhile :: A.Expression -> A.Process -> CGen ()
genWhile e p
    =  do tell ["while ("]
          genExpression e
          tell [") {\n"]
          genProcess p
          tell ["}\n"]

genPar :: A.ParMode -> [A.Process] -> CGen ()
genPar pm ps
    =  do pids <- mapM (\_ -> makeNonce "pid") ps
          sequence_ $ map genProcAlloc (zip pids ps)
          case pm of
            A.PlainPar ->
              do tell ["ProcPar ("]
                 sequence_ $ [tell [pid, ", "] | pid <- pids]
                 tell ["NULL);\n"]
            _ -> missing $ "genPar " ++ show pm
          sequence_ $ [tell ["ProcAllocClean (", pid, ");\n"] | pid <- pids]

genProcAlloc :: (String, A.Process) -> CGen ()
genProcAlloc (pid, A.ProcCall m n as)
    =  do tell ["Process *", pid, " = ProcAlloc ("]
          genName n
          ps <- get
          let fs = case fromJust $ specTypeOfName ps n of A.Proc _ fs _ -> fs
          -- FIXME stack size fixed here
          tell [", 4096"]
          sequence_ $ map (\a -> do tell [", "]
                                    genActual a) (zip as fs)
          tell [");\n"]

genProcCall :: A.Name -> [A.Actual] -> CGen ()
genProcCall n as
    =  do genName n
          ps <- get
          let fs = case fromJust $ specTypeOfName ps n of A.Proc _ fs _ -> fs
          tell [" ("]
          genActuals (zip as fs)
          tell [");\n"]
--}}}

