module TestUtil where

import qualified AST as A
import Metadata (Meta,emptyMeta)
import Monad
import Test.HUnit

m :: Meta
m = emptyMeta

--Helper function for creating an A.Name object:
simpleName :: String -> A.Name
simpleName s = A.Name { A.nameName = s , A.nameMeta = emptyMeta , A.nameType = A.VariableName }

variable :: String -> A.Variable
variable e = A.Variable m $ simpleName e

--Helper function for creating a simple variable name as an expression:
exprVariable :: String -> A.Expression
exprVariable e = A.ExprVariable m $ variable e

intLiteral :: Int -> A.Expression
intLiteral n = A.Literal m A.Int $ A.IntLiteral m (show n)

makeNamesWR :: ([String],[String]) -> ([A.Variable],[A.Variable])
makeNamesWR (x,y) = (map variable x,map variable y)

makeSimpleAssign :: String -> String -> A.Process
makeSimpleAssign dest src = A.Assign m [A.Variable m $ simpleName dest] (A.ExpressionList m [exprVariable src])

makeSeq :: [A.Process] -> A.Process
makeSeq procList = A.Seq m $ A.Several m (map (\x -> A.OnlyP m x) procList)

makePar :: [A.Process] -> A.Process
makePar procList = A.Par m A.PlainPar $ A.Several m (map (\x -> A.OnlyP m x) procList)

makeRepPar :: A.Process -> A.Process
makeRepPar proc = A.Par m A.PlainPar $ A.Rep m (A.For m (simpleName "i") (intLiteral 0) (intLiteral 3)) (A.OnlyP m proc)

assertEqualCustom :: (Show a) => String -> (a -> a -> Bool) -> a -> a -> Assertion
assertEqualCustom  preface cmp expected actual =
  unless (cmp actual expected) (assertFailure msg)
 where msg = (if null preface then "" else preface ++ "\n") ++
             "expected: " ++ show expected ++ "\n but got: " ++ show actual
