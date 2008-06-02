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

-- | A module testing things from the RainTypes module.
module RainTypesTest (ioTests) where

import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Writer
import Data.Generics
import qualified Data.Map as Map
import Test.HUnit hiding (State)

import qualified AST as A
import CompState
import Errors
import Metadata
import Pass
import Pattern
import RainTypes
import TagAST
import TestHarness
import TestUtils
import TreeUtils
import Types
import TypeUnification
import Utils

m :: Meta
m = emptyMeta

-- | Tests that constants in expressions are folded properly.  TODO these tests could do with a lot of expanding.
-- It may even be easiest to use QuickCheck for the testing.
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
   foldVar n e = TestCase $ testPass ("constantFoldTest " ++ show n) (buildExprPattern e) constantFoldPass (buildExpr e) state

   foldCon :: Int -> ExprHelper -> ExprHelper -> Test
   foldCon n exp orig = TestCase $ testPass ("constantFoldTest " ++ show n) (buildExprPattern exp) constantFoldPass (buildExpr orig) state

   state :: State CompState ()
   state = defineVariable "x" A.Int64

   lit :: Integer -> ExprHelper
   lit n = Lit $ int64Literal n

testUnify :: Test
testUnify = TestList [] {-
 [pass [] [] []
 ,pass' [("a",A.Int)] []
 ,pass' [("a",A.Int)] [("a","a")]
 ,pass2 [A.Int, A.Infer] [A.Int, A.Int]
 ,pass2 [A.List A.Int, A.List A.Infer] [A.List A.Int, A.List A.Int]
 ,fail [("a", A.Int), ("b", A.List A.Infer)] [("a","b")]
 ,fail [("a", A.Infer)] []
 ,fail [("a", A.Infer), ("b", A.Infer)] [("a","b")]

 -- Numeric things:
 ,pass2 [A.InferNum 3, A.Int32] [A.Int32, A.Int32]
 ]
 where
   pass :: [(String, A.Type)] -> [(String, String)] -> [(String, A.Type)]
     -> Test
   pass im u om = TestCase $ assertEqual "testUnify" (Right $ Map.fromList om)
                              =<< unifyRainTypes (Map.fromList $ map transformPair
                                id im) u

   fail :: [(String, A.Type)] -> [(String, String)] -> Test
   fail im u = TestCase $ case unifyRainTypes (Map.fromList im) u of
                 Left _ -> return ()
                 Right om -> assertEqual "testUnify" Nothing $ Just om

   pass' :: [(String, A.Type)] -> [(String, String)] -> Test
   pass' x y = pass x y x

   pass2 :: [A.Type] -> [A.Type] -> Test
   pass2 xs ys = pass (zip names xs) (allPairs names) (zip names ys)
     where
       names = take (min (length xs) (length ys)) $ map (:[]) ['a'..]
-}
ioTests :: IO Test
ioTests = liftM (TestLabel "RainTypesTest" . TestList) $ sequence
 [
  return constantFoldTest
  ,return testUnify
  ,automaticTest FrontendRain "testcases/automatic/unify-types-1.rain.test"
 ]
