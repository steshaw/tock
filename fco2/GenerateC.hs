-- vim:foldmethod=marker

module GenerateC where

-- FIXME: Checks should be done in the parser, not here -- for example, the
-- expressionList production should take an argument with a list of types.

-- FIXME: There should be an earlier pass across the AST that resolves Infer
-- types.

import Data.List
import Data.Maybe
import Control.Monad.Writer
import Control.Monad.Error
import Control.Monad.State

import AST
import Metadata
import ParseState
import Errors
import Types

--{{{  monad definition
type CGen a = WriterT [String] (ErrorT String (StateT ParseState IO)) a
--}}}

--{{{  top-level
generateC :: ParseState -> Process -> IO String
generateC st ast
    =  do v <- evalStateT (runErrorT (runWriterT (genTopLevel ast))) st
          case v of
            Left e -> die e
            Right (_, ss) -> return $ concat ss

genTopLevel :: Process -> CGen ()
genTopLevel p
    =  do tell ["#include <fco_support.h>\n"]
          genProcess p
--}}}

--{{{  utilities
missing :: String -> CGen ()
missing s = tell ["\nUnimplemented: ", s, "\n"]

genComma :: CGen ()
genComma = tell [", "]

makeNonce :: CGen String
makeNonce
    =  do st <- get
          let i = psNonceCounter st
          put $ st { psNonceCounter = i + 1 }
          return $ "nonce_" ++ show i

withPS :: (ParseState -> a) -> CGen a
withPS f
    =  do st <- get
          return $ f st
--}}}

--{{{  names
genName :: Name -> CGen ()
genName n = tell [[if c == '.' then '_' else c | c <- nameName n]]
--}}}

--{{{  types
genType :: Type -> CGen ()
genType Bool = tell ["bool"]
-- FIXME: This probably isn't right; we might have to explicitly cast string literals...
genType Byte = tell ["char"]
genType Int = tell ["int"]
genType Int16 = tell ["int16_t"]
genType Int32 = tell ["int32_t"]
genType Int64 = tell ["int64_t"]
genType Real32 = tell ["float"]
genType Real64 = tell ["double"]
genType (Array e t)
    =  do genType t
          tell ["["]
          genExpression e
          tell ["]"]
genType (ArrayUnsized t)
    =  do genType t
          tell ["[]"]
genType (UserDataType n) = genName n
genType (Chan t)
    =  do tell ["Channel*"]
genType (Val t)
    =  do tell ["const "]
          genType t
genType t = missing $ "genType " ++ show t
--}}}

--{{{  conversions
genConversion :: ConversionMode -> Type -> Expression -> CGen ()
genConversion DefaultConversion t e
    =  do tell ["(("]
          genType t
          tell [") "]
          genExpression e
          tell [")"]
genConversion cm t e = missing $ "genConversion " ++ show cm
--}}}

--{{{  subscripts
genSubscript :: Subscript -> CGen () -> CGen ()
genSubscript (Subscript m e) p
    =  do p
          tell ["["]
          genExpression e
          tell ["]"]
genSubscript (SubscriptTag m n) p
    =  do p
          tell ["."]
          genName n
genSubscript s p = missing $ "genSubscript " ++ show s
--}}}

--{{{  literals
genLiteral :: Literal -> CGen ()
genLiteral (Literal m t lr) = genLiteralRepr lr
genLiteral l = missing $ "genLiteral " ++ show l

genLiteralRepr :: LiteralRepr -> CGen ()
genLiteralRepr (RealLiteral m s) = tell [s]
genLiteralRepr (IntLiteral m s) = tell [s]
genLiteralRepr (HexLiteral m s) = case s of ('#':rest) -> tell ["0x", rest]
genLiteralRepr (ByteLiteral m s) = tell ["'", convStringLiteral s, "'"]
genLiteralRepr (StringLiteral m s) = tell ["\"", convStringLiteral s, "\""]
genLiteralRepr (ArrayLiteral m es)
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
genChannel :: Channel -> CGen ()
genChannel (Channel m n) = genName n
genChannel (SubscriptedChannel m s c) = genSubscript s (genChannel c)

genVariable :: Variable -> CGen ()
genVariable (Variable m n) = genName n
genVariable (SubscriptedVariable m s v) = genSubscript s (genVariable v)
--}}}

--{{{  expressions
genExpression :: Expression -> CGen ()
genExpression (Monadic m op e) = genMonadic op e
genExpression (Dyadic m op e f) = genDyadic op e f
genExpression (MostPos m t) = genTypeConstant "mostpos" t
genExpression (MostNeg m t) = genTypeConstant "mostneg" t
--genExpression (Size m t)
genExpression (Conversion m cm t e) = genConversion cm t e
genExpression (ExprVariable m v) = genVariable v
genExpression (ExprLiteral m l) = genLiteral l
genExpression (AST.True m) = tell ["true"]
genExpression (AST.False m) = tell ["false"]
--genExpression (FunctionCall m n es)
--genExpression (SubscriptedExpr m s e)
--genExpression (BytesInExpr m e)
genExpression (BytesInType m t)
    =  do tell ["sizeof ("]
          genType t
          tell [")"]
--genExpression (OffsetOf m t n)
genExpression t = missing $ "genExpression " ++ show t

genTypeConstant :: String -> Type -> CGen ()
genTypeConstant s t = missing $ "genTypeConstant " ++ show t
--}}}

--{{{  operators
genSimpleMonadic :: String -> Expression -> CGen ()
genSimpleMonadic s e
    =  do tell ["(", s]
          genExpression e
          tell [")"]

genMonadic :: MonadicOp -> Expression -> CGen ()
genMonadic MonadicSubtr e = genSimpleMonadic "-" e
genMonadic MonadicBitNot e = genSimpleMonadic "~" e
genMonadic MonadicNot e = genSimpleMonadic "!" e
--genMonadic MonadicSize e
genMonadic op e = missing $ "genMonadic " ++ show op

genSimpleDyadic :: String -> Expression -> Expression -> CGen ()
genSimpleDyadic s e f
    =  do tell ["("]
          genExpression e
          tell [" ", s, " "]
          genExpression f
          tell [")"]

genFuncDyadic :: String -> Expression -> Expression -> CGen ()
genFuncDyadic s e f
    =  do tell [s, " ("]
          genExpression e
          tell [", "]
          genExpression f
          tell [")"]

genDyadic :: DyadicOp -> Expression -> Expression -> CGen ()
genDyadic Add e f = genFuncDyadic "occam_add" e f
genDyadic Subtr e f = genFuncDyadic "occam_subtr" e f
genDyadic Mul e f = genFuncDyadic "occam_mul" e f
genDyadic Div e f = genFuncDyadic "occam_div" e f
genDyadic Rem e f = genFuncDyadic "occam_rem" e f
genDyadic Plus e f = genSimpleDyadic "+" e f
genDyadic Minus e f = genSimpleDyadic "-" e f
genDyadic Times e f = genSimpleDyadic "*" e f
genDyadic BitAnd e f = genSimpleDyadic "&" e f
genDyadic BitOr e f = genSimpleDyadic "|" e f
genDyadic BitXor e f = genSimpleDyadic "^" e f
genDyadic And e f = genSimpleDyadic "&&" e f
genDyadic Or e f = genSimpleDyadic "||" e f
genDyadic Eq e f = genSimpleDyadic "==" e f
genDyadic NotEq e f = genSimpleDyadic "!=" e f
genDyadic Less e f = genSimpleDyadic "<" e f
genDyadic More e f = genSimpleDyadic ">" e f
genDyadic LessEq e f = genSimpleDyadic "<=" e f
genDyadic MoreEq e f = genSimpleDyadic ">=" e f
genDyadic After e f = genFuncDyadic "occam_after" e f
--}}}

--{{{  input/output items
genInputItem :: Channel -> InputItem -> CGen ()
genInputItem c (InCounted m cv av)
    =  do genInputItem c (InVariable m cv)
          -- need to then input as much as appropriate
          missing "genInputItem counted"
genInputItem c (InVariable m v)
    =  do ps <- get
          let t = fromJust $ typeOfVariable ps v
          case t of
            Int ->
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

genOutputItem :: Channel -> OutputItem -> CGen ()
genOutputItem c (OutCounted m ce ae)
    =  do genOutputItem c (OutExpression m ce)
          missing "genOutputItem counted"
genOutputItem c (OutExpression m e)
    =  do n <- makeNonce
          ps <- get
          let t = fromJust $ typeOfExpression ps e
          case t of
            Int ->
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
--}}}

--{{{  choice/alternatives/options/variants
--}}}

--{{{  structured
--}}}

--{{{  specifications
genSpec :: Meta -> Specification -> CGen () -> CGen ()
genSpec m spec body
    =  do introduceSpec spec
          body
          removeSpec spec

introduceSpec :: Specification -> CGen ()
introduceSpec (n, Declaration m Timer) = return ()
introduceSpec (n, Declaration m t)
    =  do case t of
            Chan _ -> do cn <- makeNonce
                         tell ["Channel ", cn, ";\n"]
                         tell ["ChanInit (&", cn, ");\n"]
                         tell ["Channel *"]
                         genName n
                         tell [" = &", cn, ";\n"]
            _ -> do genType t
                    tell [" "]
                    genName n
                    tell [";\n"]
introduceSpec (n, Is m t v)
    =  do genType t
          tell ["& "]
          genName n
          tell [" = "]
          genVariable v
          tell [";\n"]
introduceSpec (n, ValIs m t e)
    =  do tell ["const "]
          genType t
          tell [" "]
          genName n
          tell [" = "]
          genExpression e
          tell [";\n"]
introduceSpec (n, IsChannel m t c)
    =  do genType t
          tell [" "]
          genName n
          tell [" = "]
          genChannel c
          tell [";\n"]
introduceSpec (n, IsChannelArray m t cs)
    =  do genType t
          tell [" "]
          genName n
          tell [" = {"]
          sequence_ $ intersperse genComma (map genChannel cs)
          tell ["};\n"]
introduceSpec (n, Proc m fs p)
    =  do tell ["void "]
          genName n
          tell [" ("]
          genFormals fs
          tell [") {\n"]
          genProcess p
          tell ["}\n"]
-- CASE protocol should generate an enum for the tags
introduceSpec (n, t) = missing $ "introduceSpec " ++ show t

removeSpec :: Specification -> CGen ()
removeSpec _ = return ()
--}}}

--{{{  actuals/formals
genActuals :: [Actual] -> CGen ()
genActuals as = sequence_ $ intersperse genComma (map genActual as)

genActual :: Actual -> CGen ()
genActual (ActualExpression e) = genExpression e
genActual (ActualChannel c) = genChannel c

genFormals :: Formals -> CGen ()
genFormals fs = sequence_ $ intersperse genComma (map genFormal fs)

-- Arrays must be handled specially
genFormal :: (Type, Name) -> CGen ()
genFormal (ft, n)
    =  do case ft of
            Val t ->
              do tell ["const "]
                 genType t
                 tell [" "]
            Chan t ->
              tell ["Channel *"]
            _ ->
              do genType ft
                 tell ["& "]
          genName n
--}}}

--{{{  par modes
--}}}

--{{{  processes
genProcess :: Process -> CGen ()
genProcess p = case p of
  ProcSpec m s p -> genSpec m s (genProcess p)
  Assign m vs es -> genAssign vs es
  Input m c im -> genInput c im
  Output m c ois -> genOutput c ois
  --OutputCase m c t ois
  Skip m -> tell ["/* skip */\n"]
  Stop m -> tell ["SetErr ();\n"]
  Main m -> tell ["/* main */\n"]
  Seq m ps -> sequence_ $ map genProcess ps
  --SeqRep m r p
  --If m s
  --Case m e s
  While m e p -> genWhile e p
  --Par m pm ps
  --ParRep m pm r p
  --Processor m e p
  --Alt m b s
  ProcCall m n as -> genProcCall n as
  _ -> missing $ "genProcess " ++ show p

genAssign :: [Variable] -> ExpressionList -> CGen ()
genAssign vs el
    = case el of
        FunctionCallList m n es -> missing "function call"
        ExpressionList m es -> case vs of
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

genInput :: Channel -> InputMode -> CGen ()
genInput c im
    =  do ps <- get
          let t = fromJust $ typeOfChannel ps c
          case t of
            Timer -> case im of 
                       InputSimple m [InVariable m' v] -> genTimerRead v
                       InputAfter m e -> genTimerWait e
            _ -> case im of
                   InputSimple m is -> sequence_ $ map (genInputItem c) is
                   _ -> missing $ "genInput " ++ show im

genTimerRead :: Variable -> CGen ()
genTimerRead v
    =  do n <- makeNonce
          tell ["{\n"]
          tell ["Time ", n, ";\n"]
          tell ["ProcTime (&", n, ");\n"]
          genVariable v
          tell [" = ", n, ";\n"]
          tell ["}\n"]

genTimerWait :: Expression -> CGen ()
genTimerWait e
    =  do tell ["ProcTimeAfter ("]
          genExpression e
          tell [");\n"]

genOutput :: Channel -> [OutputItem] -> CGen ()
genOutput c ois = sequence_ $ map (genOutputItem c) ois

genWhile :: Expression -> Process -> CGen ()
genWhile e p
    =  do tell ["while ("]
          genExpression e
          tell [") {\n"]
          genProcess p
          tell ["}\n"]

genProcCall :: Name -> [Actual] -> CGen ()
genProcCall n as
    =  do genName n
          tell [" ("]
          genActuals as
          tell [");\n"]
--}}}

