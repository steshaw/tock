-- | Generate C++ code from the mangled AST.
module GenerateC where

-- FIXME: Checks should be done in the parser, not here -- for example, the
-- expressionList production should take an argument with a list of types.

-- FIXME: There should be a pass that pulls PAR branches (that aren't already
-- PROC calls) out into PROCs.

-- FIXME: Arrays. Should be a struct that contains the data and size, and we
-- then use a pointer to the struct to pass around.

-- FIXME: The show instance for types should produce occam-looking types.

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
--}}}

--{{{  names
genName :: A.Name -> CGen ()
genName n = tell [[if c == '.' then '_' else c | c <- A.nameName n]]
--}}}

--{{{  types
genType :: A.Type -> CGen ()
genType A.Bool = tell ["bool"]
-- FIXME: This probably isn't right; we might have to explicitly cast string literals...
genType A.Byte = tell ["char"]
genType A.Int = tell ["int"]
genType A.Int16 = tell ["int16_t"]
genType A.Int32 = tell ["int32_t"]
genType A.Int64 = tell ["int64_t"]
genType A.Real32 = tell ["float"]
genType A.Real64 = tell ["double"]
genType (A.Array e t)
    =  do genType t
          tell ["["]
          genExpression e
          tell ["]"]
genType (A.ArrayUnsized t)
    =  do genType t
          tell ["[]"]
genType (A.UserDataType n) = genName n
genType (A.Chan t)
    =  do tell ["Channel*"]
genType t = missing $ "genType " ++ show t
--}}}

--{{{  abbreviations
genConst :: A.AbbrevMode -> CGen ()
genConst A.Abbrev = return ()
genConst A.ValAbbrev = tell ["const "]
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

--{{{  channels, variables
genChannel :: A.Channel -> CGen ()
genChannel (A.Channel m n) = genName n
genChannel (A.SubscriptedChannel m s c) = genSubscript s (genChannel c)

genVariable :: A.Variable -> CGen ()
genVariable (A.Variable m n) = genName n
genVariable (A.SubscriptedVariable m s v) = genSubscript s (genVariable v)
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
genExpression (A.BytesInType m t)
    =  do tell ["sizeof ("]
          genType t
          tell [")"]
--genExpression (A.OffsetOf m t n)
genExpression t = missing $ "genExpression " ++ show t

genTypeConstant :: String -> A.Type -> CGen ()
genTypeConstant s t = missing $ "genTypeConstant " ++ show t
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
--genMonadic A.MonadicSize e
genMonadic op e = missing $ "genMonadic " ++ show op

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
genInputItem :: A.Channel -> A.InputItem -> CGen ()
genInputItem c (A.InCounted m cv av)
    =  do genInputItem c (A.InVariable m cv)
          -- need to then input as much as appropriate
          missing "genInputItem counted"
genInputItem c (A.InVariable m v)
    =  do ps <- get
          let t = fromJust $ typeOfVariable ps v
          case t of
            A.Int ->
              do tell ["ChanInInt ("]
                 genChannel c
                 tell [", &"]
                 genVariable v
                 tell [");\n"]
            _ ->
              do tell ["ChanIn ("]
                 genChannel c
                 tell [", &"]
                 genVariable v
                 tell [", sizeof ("]
                 genType t
                 tell ["));\n"]

genOutputItem :: A.Channel -> A.OutputItem -> CGen ()
genOutputItem c (A.OutCounted m ce ae)
    =  do genOutputItem c (A.OutExpression m ce)
          missing "genOutputItem counted"
genOutputItem c (A.OutExpression m e)
    =  do n <- makeNonce
          ps <- get
          let t = fromJust $ typeOfExpression ps e
          case t of
            A.Int ->
              do tell ["ChanOutInt ("]
                 genChannel c
                 tell [", "]
                 genExpression e
                 tell [");\n"]
            _ ->
              do tell ["{\n"]
                 genType t
                 tell [" ", n, " = "]
                 genExpression e
                 tell [";\n"]
                 tell ["ChanOut ("]
                 genChannel c
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
    =  do counter <- makeNonce
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

--{{{  specifications
genSpec :: A.Specification -> CGen () -> CGen ()
genSpec spec body
    =  do introduceSpec spec
          body
          removeSpec spec

introduceSpec :: A.Specification -> CGen ()
introduceSpec (n, A.Declaration m A.Timer) = return ()
introduceSpec (n, A.Declaration m t)
    =  do case t of
            A.Chan _ ->
              do cn <- makeNonce
                 tell ["Channel ", cn, ";\n"]
                 tell ["ChanInit (&", cn, ");\n"]
                 tell ["Channel *"]
                 genName n
                 tell [" = &", cn, ";\n"]
            _ ->
              do genType t
                 tell [" "]
                 genName n
                 tell [";\n"]
introduceSpec (n, A.Is m am t v)
    =  do genConst am
          genType t
          tell ["& "]
          genName n
          tell [" = "]
          genVariable v
          tell [";\n"]
introduceSpec (n, A.IsExpr m am t e)
    =  do genConst am
          genType t
          tell [" "]
          genName n
          tell [" = "]
          genExpression e
          tell [";\n"]
introduceSpec (n, A.IsChannel m t c)
    =  do genType t
          tell [" "]
          genName n
          tell [" = "]
          genChannel c
          tell [";\n"]
introduceSpec (n, A.IsChannelArray m t cs)
    =  do genType t
          tell [" "]
          genName n
          tell [" = {"]
          sequence_ $ intersperse genComma (map genChannel cs)
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
removeSpec _ = return ()
--}}}

--{{{  actuals/formals
genActuals :: [A.Actual] -> CGen ()
genActuals as = sequence_ $ intersperse genComma (map genActual as)

genActual :: A.Actual -> CGen ()
genActual (A.ActualExpression e) = genExpression e
genActual (A.ActualChannel c) = genChannel c

genFormals :: [A.Formal] -> CGen ()
genFormals fs = sequence_ $ intersperse genComma (map genFormal fs)

-- Arrays must be handled specially
genFormal :: A.Formal -> CGen ()
genFormal (A.Formal am t n)
    =  do case am of
            A.ValAbbrev ->
              do genConst am
                 genType t
                 tell [" "]
            A.Abbrev ->
              do genType t
                 tell ["& "]
          genName n
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
               ns <- mapM (\_ -> makeNonce) vs
               mapM (\(v, n, e) -> do st <- get
                                      let t = typeOfVariable st v
                                      genType (fromJust t)
                                      tell [" ", n, " = "]
                                      genExpression e
                                      tell [";\n"])
                    (zip3 vs ns es)
               mapM (\(v, n) -> do genVariable v
                                   tell [" = ", n, ";\n"])
                    (zip vs ns)
               tell ["}\n"]

genInput :: A.Channel -> A.InputMode -> CGen ()
genInput c im
    =  do ps <- get
          let t = fromJust $ typeOfChannel ps c
          case t of
            A.Timer -> case im of 
              A.InputSimple m [A.InVariable m' v] -> genTimerRead v
              A.InputAfter m e -> genTimerWait e
            _ -> case im of
              A.InputSimple m is -> sequence_ $ map (genInputItem c) is
              _ -> missing $ "genInput " ++ show im

genTimerRead :: A.Variable -> CGen ()
genTimerRead v
    =  do n <- makeNonce
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

genOutput :: A.Channel -> [A.OutputItem] -> CGen ()
genOutput c ois = sequence_ $ map (genOutputItem c) ois

genStop :: CGen ()
genStop = tell ["SetErr ();\n"]

-- FIXME: This could be special-cased to generate if ... else if ... for bits
-- that aren't replicated and don't have specs.
genIf :: A.Structured -> CGen ()
genIf s
    =  do label <- makeNonce
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

-- FIXME Stubbed out for now so I can see what the branches look like...
genPar :: A.ParMode -> [A.Process] -> CGen ()
genPar pm ps
    =  do tell ["#error PAR not implemented\n"]
          sequence_ $ map genProcess ps
          tell ["#error end PAR\n"]

genProcCall :: A.Name -> [A.Actual] -> CGen ()
genProcCall n as
    =  do genName n
          tell [" ("]
          genActuals as
          tell [");\n"]
--}}}

