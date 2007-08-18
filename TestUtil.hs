{-
Tock: a compiler for parallel languages
Copyright (C) 2007  University of Kent

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

makeAssign :: A.Variable -> A.Expression -> A.Process
makeAssign v e = A.Assign m [v] $ A.ExpressionList m [e]

 
makeLiteralString :: String -> A.Expression
makeLiteralString str = A.Literal m (A.Array [A.Dimension (length str)] A.Byte) (A.ArrayLiteral m (map makeLiteralChar str))
  where
    makeLiteralChar :: Char -> A.ArrayElem
    makeLiteralChar c = A.ArrayElemExpr $ A.Literal m A.Byte (A.ByteLiteral m [c] {-(show (fromEnum c))-})


assertCompareCustom :: (Show a) => String -> (a -> a -> Bool) -> a -> a -> Assertion
assertCompareCustom  preface cmp expected actual =
  unless (cmp actual expected) (assertFailure msg)
 where msg = (if null preface then "" else preface ++ "\n") ++
             "expected: " ++ show expected ++ "\n*** got: " ++ show actual

assertNotEqual :: (Show a,Eq a) => String -> a -> a -> Assertion
assertNotEqual msg = assertCompareCustom msg (/=)
