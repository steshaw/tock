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

module RainTypesTest where

import Test.HUnit hiding (State)
import TestUtil
import RainTypes
import TreeUtil
import Pattern
import qualified AST as A
import CompState
import Control.Monad.State

constantFoldTest :: Test
constantFoldTest = TestList
 [
  foldVar 0 $ Var "x"
  ,foldVar 1 $ Dy (Var "x") A.Plus (lit 0)
  
  ,foldCon 100 (lit 2) (Dy (lit 1) A.Plus (lit 1))  
  ,foldCon 101 (lit 65537) (Dy (lit 2) A.Plus (lit 65535))
  ,foldCon 102 (lit (- two63)) (Dy (lit $ two63 - 1) A.Plus (lit 1))
  
  ,foldCon 110 (Dy (Var "x") A.Plus (lit 2)) (Dy (Var "x") A.Plus (Dy (lit 1) A.Plus (lit 1)))
 ]
 where
   two63 :: Integer
   two63 = 9223372036854775808
 
   foldVar :: Int -> ExprHelper -> Test
   foldVar n e = testPass ("constantFoldTest " ++ show n) (buildExprPattern e) (constantFoldPass $ buildExpr e) state

   foldCon :: Int -> ExprHelper -> ExprHelper -> Test
   foldCon n exp orig = testPass ("constantFoldTest " ++ show n) (buildExprPattern exp) (constantFoldPass $ buildExpr orig) state

   state :: State CompState ()
   state = return ()

   lit :: Integer -> ExprHelper
   lit n = Lit $ int64Literal n

annotateIntTest :: Test
annotateIntTest = TestList
 [
  failSigned (-9223372036854775809)
  ,signed A.Int64 (-9223372036854775808)
  ,signed A.Int64 (-2147483649)
  ,signed A.Int32 (-2147483648)
  ,signed A.Int32 (-32769)
  ,signed A.Int16 (-32768)
  ,signed A.Int16 (-129)
  ,signed A.Int8 (-128)
  ,signed A.Int8 0
  ,signed A.Int8 127
  ,signed A.Int16 128
  ,signed A.Int16 32767
  ,signed A.Int32 32768
  ,signed A.Int32 2147483647
  ,signed A.Int64 2147483648
  ,signed A.Int64 9223372036854775807
  ,failSigned 9223372036854775808
 ]
 where
  signed :: A.Type -> Integer -> Test
  signed t n = testPass ("annotateIntTest: " ++ show n) (tag3 A.Literal DontCare t $ tag2 A.IntLiteral DontCare (show n)) 
    (annnotateIntLiteralTypes $ int64Literal n) (return ())
  failSigned :: Integer -> Test
  failSigned n = testPassShouldFail ("annotateIntTest: " ++ show n) (annnotateIntLiteralTypes $ int64Literal n) (return ())

tests :: Test
tests = TestList
 [
  constantFoldTest
  ,annotateIntTest
 ]
