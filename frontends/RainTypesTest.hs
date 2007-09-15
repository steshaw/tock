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
import Control.Monad.Error
import Types
import Pass

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
   foldVar n e = TestCase $ testPass ("constantFoldTest " ++ show n) (buildExprPattern e) (constantFoldPass $ buildExpr e) state

   foldCon :: Int -> ExprHelper -> ExprHelper -> Test
   foldCon n exp orig = TestCase $ testPass ("constantFoldTest " ++ show n) (buildExprPattern exp) (constantFoldPass $ buildExpr orig) state

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
  signed t n = TestCase $ testPass ("annotateIntTest: " ++ show n) (tag3 A.Literal DontCare t $ tag2 A.IntLiteral DontCare (show n)) 
    (annnotateIntLiteralTypes $ int64Literal n) (return ())
  failSigned :: Integer -> Test
  failSigned n = TestCase $ testPassShouldFail ("annotateIntTest: " ++ show n) (annnotateIntLiteralTypes $ int64Literal n) (return ())

checkExpressionTest :: Test
checkExpressionTest = TestList
 [
  passSame 0 A.Int64 $ Dy (Var "x") A.Plus (Var "x")
  ,passSame 1 A.Byte $ Dy (Var "xu8") A.Plus (Var "xu8")
  
  ,pass 100 A.Int64 (Dy (Var "x") A.Plus (Cast A.Int64 $ Var "xu8")) (Dy (Var "x") A.Plus (Var "xu8"))
  ,pass 101 A.Int32 (Dy (Cast A.Int32 $ Var "x16") A.Plus (Cast A.Int32 $ Var "xu16")) (Dy (Var "x16") A.Plus (Var "xu16"))
  
  ,pass 200 A.Int64 (Dy (Var "x") A.Plus (Cast A.Int64 $ Cast A.Int32 $ Var "xu8")) (Dy (Var "x") A.Plus (Cast A.Int32 $ Var "xu8"))
  
  ,fail 300 $ Dy (Var "x") A.Plus (Var "xu64")
  
  ,pass 400 A.Int16 (Dy (Var "x16") A.Plus (Cast A.Int16 $ int A.Int8 100)) (Dy (Var "x16") A.Plus (int A.Int8 100))
  ,pass 401 A.Int16 (Dy (Cast A.Int16 $ Var "x8") A.Plus (int A.Int16 200)) (Dy (Var "x8") A.Plus (int A.Int16 200))
  --This fails because you are trying to add a signed constant to an unsigned integer that cannot be expanded:
  ,fail 402 $ Dy (Var "xu64") A.Plus (int A.Int64 0)
 ]
 where
  passSame :: Int -> A.Type -> ExprHelper -> Test
  passSame n t e = pass n t e e
  
  pass :: Int -> A.Type -> ExprHelper -> ExprHelper -> Test
  pass n t exp act = TestCase $ pass' n t (buildExprPattern exp) (buildExpr act)

  --To easily get more tests, we take the result of every successful pass (which must be fine now), and feed it back through
  --the type-checker to check that it is unchanged
  
  pass' :: Int -> A.Type -> Pattern -> A.Expression -> Assertion
  pass' n t exp act = testPassWithCheck ("checkExpressionTest " ++ show n) exp (checkExpressionTypes act) state (check t)   
    where
      check :: A.Type -> A.Expression -> Assertion
      check t e
        = do eot <- errorOrType
             case eot of
               Left err -> assertFailure ("checkExpressionTest " ++ show n ++ " typeOfExpression failed")
               Right t' -> do assertEqual ("checkExpressionTest " ++ show n) t t'
                              --Now feed it through again, to make sure it isn't changed:
                              if (e /= act) then pass' (10000 + n) t (mkPattern e) e else return ()
            where
              errorOrType :: IO (Either String A.Type)
              errorOrType = evalStateT (runErrorT $ typeOfExpression e) (execState state emptyState)
  
  
  fail :: Int -> ExprHelper -> Test
  fail n e = TestCase $ testPassShouldFail ("checkExpressionTest " ++ show n) (checkExpressionTypes $ buildExpr e) state
  
  int :: A.Type -> Integer -> ExprHelper
  int t n = Lit $ A.Literal m t $ A.IntLiteral m (show n)

  defVar :: String -> A.Type -> State CompState ()
  defVar n t = defineName (simpleName n) $ simpleDefDecl n t
  
  state :: State CompState ()
  state = do defVar "x" A.Int64
             defVar "b" A.Bool
             defVar "xu8" A.Byte
             defVar "xu16" A.UInt16
             defVar "xu32" A.UInt32
             defVar "xu64" A.UInt64
             defVar "x16" A.Int16
             defVar "x8" A.Int16

tests :: Test
tests = TestList
 [
  constantFoldTest
  ,annotateIntTest
  ,checkExpressionTest
 ]
