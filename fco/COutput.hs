-- Write C code

module COutput where

import List
import Data.Generics
import qualified AST as A

concatWith x l = concat $ intersperse x l
bracketed s = "(" ++ s ++ ")"

unimp :: Data a => a -> String
unimp = unimpG `extQ` unimpS
  where
    unimpG :: Data a => a -> String
    unimpG t = rep
      where
        ctr = showConstr $ toConstr t
        items = gmapQ unimp t
        rep = "(" ++ ctr ++ concat [' ' : s | s <- items] ++ ")"

    unimpS :: String -> String
    unimpS s = show s

writeC :: A.Process -> String
writeC p = header ++ doProcess p
  where
    header = "#include <stdint.h>\n"

    doName :: A.Name -> String
    doName (A.Name n) = n

    doUserType :: A.Type -> String
    doUserType (A.UserType (A.Name n)) = "usertype_" ++ n

    doType :: A.Type -> String
    doType (A.Val t) = "const " ++ (doType t)
    doType A.Bool = "int8_t"
    doType A.Byte = "uint8_t"
    doType A.Int = "int32_t"
    doType A.Int16 = "int16_t"
    doType A.Int32 = "int32_t"
    doType A.Int64 = "int64_t"
    doType A.Real32 = "float"
    doType A.Real64 = "double"
    doType u@(A.UserType _) = doUserType u
    doType t = unimp t

    doVariable :: A.Variable -> String
    doVariable (A.Variable n) = doName n

    doLiteralRepr :: A.LiteralRepr -> String
    doLiteralRepr r = case r of
      A.IntLiteral s -> s

    doLiteral :: A.Literal -> String
    doLiteral (A.Literal t r) = doLiteralRepr r

    doFunction :: A.ValueProcess -> String
    doFunction (A.ValOfSpec s p) = doSpecification s ++ doFunction p
    doFunction (A.ValOf p el) = doProcess p ++ "return " ++ doExpressionListOne el ++ ";\n"
    -- FIXME handle multi-value return

    makeDecl :: A.Type -> A.Name -> String
    makeDecl t n = doType t ++ " " ++ doName n

    makeFormals :: [(A.Type, A.Name)] -> String
    makeFormals fs = "(" ++ concatWith ", " [makeDecl t n | (t, n) <- fs] ++ ")"

    doSpecification :: A.Specification -> String
    doSpecification s@(n, st) = case st of
      A.Declaration t -> makeDecl t n ++ ";\n"
      A.Proc fs p -> "void " ++ doName n ++ " " ++ makeFormals fs ++ " {\n" ++ doProcess p ++ "}\n"
      A.Function [r] fs vp -> doType r ++ " " ++ doName n ++ " " ++ makeFormals fs ++ " {\n" ++ doFunction vp ++ "}\n"
      _ -> unimp s

    doProcSpec :: A.Process -> String
    doProcSpec p = doP [] p
      where
        doP :: [A.Specification] -> A.Process -> String
        doP ss (A.ProcSpec s p) = doP (ss ++ [s]) p
        doP ss p = "{\n" ++ concat (map doSpecification ss) ++ doProcess p ++ "}\n"

    doActuals :: [A.Expression] -> String
    doActuals es = "(" ++ concatWith ", " (map doExpression es) ++ ")"

    doFunctionCall :: A.Name -> [A.Expression] -> String
    doFunctionCall n as = (doName n) ++ " " ++ doActuals as

    doMonadic :: A.MonadicOp -> A.Expression -> String
    doMonadic o a = case o of
      A.MonadicSubtr -> "-" ++ doExpression a

    doDyadic :: A.DyadicOp -> A.Expression -> A.Expression -> String
    doDyadic o a b = bracketed $ case o of
      -- FIXME Ops ought to be runtime-checked using inline functions
      A.Add -> doExpression a ++ " + " ++ doExpression b
      A.Subtr -> doExpression a ++ " - " ++ doExpression b
      A.Mul -> doExpression a ++ " * " ++ doExpression b
      A.Div -> doExpression a ++ " / " ++ doExpression b

    doExpression :: A.Expression -> String
    doExpression e = case e of
      A.Monadic o a -> doMonadic o a
      A.Dyadic o a b -> doDyadic o a b
      A.ExprVariable v -> doVariable v
      A.ExprLiteral l -> doLiteral l

    doExpressionListOne :: A.ExpressionList -> String
    doExpressionListOne e = case e of
      A.FunctionCallList n as -> doFunctionCall n as
      A.ExpressionList [e] -> doExpression e

    doAssign :: A.Process -> String
    doAssign a = case a of
      A.Assign [v] el -> (doVariable v) ++ " = " ++ (doExpressionListOne el) ++ ";\n"

    doProcess :: A.Process -> String
    doProcess s@(A.ProcSpec _ _) = doProcSpec s
    doProcess a@(A.Assign _ _) = doAssign a
    doProcess A.Skip = "/* SKIP */;\n"
    doProcess A.Stop = "SetErr ();\n"
    doProcess A.Main = "/* MAIN-PROCESS */\n";
    doProcess (A.Seq ps) = concatWith "" (map doProcess ps)
    doProcess (A.ProcCall n as) = doName n ++ " " ++ doActuals as ++ ";\n"
    doProcess n = unimp n

