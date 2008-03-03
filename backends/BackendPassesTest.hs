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

-- #ignore-exports

-- | Currently contains tests just for the transformWaitFor pass that is run for the C backend.
module BackendPassesTest (tests) where

import Control.Monad.State
import qualified Data.Map as Map
import Test.HUnit hiding (State)

import qualified AST as A
import BackendPasses
import CompState
import Metadata
import Pattern
import TagAST
import TestUtils
import TreeUtils

m :: Meta
m = emptyMeta

-- | Test WaitUntil guard (should be unchanged)
testTransformWaitFor0 :: Test
testTransformWaitFor0 = TestCase $ testPass "testTransformWaitFor0" orig (transformWaitFor orig) (return ())
  where
    orig = A.Alt m True $ A.Only m $ A.AlternativeWait m A.WaitUntil (exprVariable "t") (A.Skip m)
    
-- | Test pulling out a single WaitFor:
testTransformWaitFor1 :: Test
testTransformWaitFor1 = TestCase $ testPass "testTransformWaitFor1" exp (transformWaitFor orig) (return ())
  where
    orig = A.Alt m True $ A.Only m $ A.AlternativeWait m A.WaitFor (exprVariable "t") (A.Skip m)
    exp = tag2 A.Seq DontCare $ mSpecP (tag3 A.Specification DontCare varName $ A.Declaration m A.Time Nothing) $
            mSeveralP
              [
                mOnlyP $ tag2 A.GetTime DontCare var
                ,mOnlyP $ tag3 A.Assign DontCare [var] $ tag2 A.ExpressionList DontCare [tag4 A.Dyadic DontCare A.Plus evar (exprVariablePattern "t")]
                ,mOnlyP $ tag3 A.Alt DontCare True $ mOnlyA $ tag4 A.AlternativeWait DontCare A.WaitUntil evar (A.Skip m)
              ]
    varName = (tag3 A.Name DontCare A.VariableName $ Named "nowt" DontCare)
    var = tag2 A.Variable DontCare varName
    evar = tag2 A.ExprVariable DontCare var

-- | Test pulling out two WaitFors:
testTransformWaitFor2 :: Test
testTransformWaitFor2 = TestCase $ testPass "testTransformWaitFor2" exp (transformWaitFor orig) (return ())
  where
    orig = A.Alt m True $ A.Several m [A.Only m $ A.AlternativeWait m A.WaitFor (exprVariable "t0") (A.Skip m),
                                       A.Only m $ A.AlternativeWait m A.WaitFor (exprVariable "t1") (A.Skip m)]
    exp = tag2 A.Seq DontCare $ mSpecP (tag3 A.Specification DontCare varName0 $ A.Declaration m A.Time Nothing) $
          mSpecP (tag3 A.Specification DontCare varName1 $ A.Declaration m A.Time Nothing) $
            mSeveralP
              [
                mOnlyP $ tag2 A.GetTime DontCare var0
                ,mOnlyP $ tag3 A.Assign DontCare [var0] $ tag2 A.ExpressionList DontCare [tag4 A.Dyadic DontCare A.Plus evar0 (exprVariablePattern "t0")]
                ,mOnlyP $ tag2 A.GetTime DontCare var1
                ,mOnlyP $ tag3 A.Assign DontCare [var1] $ tag2 A.ExpressionList DontCare [tag4 A.Dyadic DontCare A.Plus evar1 (exprVariablePattern "t1")]
                ,mOnlyP $ tag3 A.Alt DontCare True $ mSeveralA
                  [mOnlyA $ tag4 A.AlternativeWait DontCare A.WaitUntil evar0 (A.Skip m)
                  ,mOnlyA $ tag4 A.AlternativeWait DontCare A.WaitUntil evar1 (A.Skip m)]
              ]
    varName0 = (tag3 A.Name DontCare A.VariableName $ Named "nowt0" DontCare)
    var0 = tag2 A.Variable DontCare varName0
    evar0 = tag2 A.ExprVariable DontCare var0
    varName1 = (tag3 A.Name DontCare A.VariableName $ Named "nowt1" DontCare)
    var1 = tag2 A.Variable DontCare varName1
    evar1 = tag2 A.ExprVariable DontCare var1

-- | Test pulling out a single WaitFor with an expression:
testTransformWaitFor3 :: Test
testTransformWaitFor3 = TestCase $ testPass "testTransformWaitFor3" exp (transformWaitFor orig) (return ())
  where
    orig = A.Alt m True $ A.Only m $ A.AlternativeWait m A.WaitFor (A.Dyadic m A.Plus (exprVariable "t0") (exprVariable "t1")) (A.Skip m)
    exp = tag2 A.Seq DontCare $ mSpecP (tag3 A.Specification DontCare varName $ A.Declaration m A.Time Nothing) $
            mSeveralP
              [
                mOnlyP $ tag2 A.GetTime DontCare var
                ,mOnlyP $ tag3 A.Assign DontCare [var] $ tag2 A.ExpressionList DontCare [tag4 A.Dyadic DontCare A.Plus evar 
                  (A.Dyadic m A.Plus (exprVariable "t0") (exprVariable "t1"))]
                ,mOnlyP $ tag3 A.Alt DontCare True $ mOnlyA $ tag4 A.AlternativeWait DontCare A.WaitUntil evar (A.Skip m)
              ]
    varName = (tag3 A.Name DontCare A.VariableName $ Named "nowt" DontCare)
    var = tag2 A.Variable DontCare varName
    evar = tag2 A.ExprVariable DontCare var

-- | Test pulling out a single WaitFor with some slight nesting in the ALT:
testTransformWaitFor4 :: Test
testTransformWaitFor4 = TestCase $ testPass "testTransformWaitFor4" exp (transformWaitFor orig) (return ())
  where
    orig = A.Alt m True $ A.Several m [A.Only m $ A.AlternativeWait m A.WaitFor (exprVariable "t") (A.Skip m)]
    exp = tag2 A.Seq DontCare $ mSpecP (tag3 A.Specification DontCare varName $ A.Declaration m A.Time Nothing) $
            mSeveralP
              [
                mOnlyP $ tag2 A.GetTime DontCare var
                ,mOnlyP $ tag3 A.Assign DontCare [var] $ tag2 A.ExpressionList DontCare [tag4 A.Dyadic DontCare A.Plus evar (exprVariablePattern "t")]
                ,mOnlyP $ tag3 A.Alt DontCare True $ mSeveralA
                  [mOnlyA $ tag4 A.AlternativeWait DontCare A.WaitUntil evar (A.Skip m)]
              ]
    varName = (tag3 A.Name DontCare A.VariableName $ Named "nowt" DontCare)
    var = tag2 A.Variable DontCare varName
    evar = tag2 A.ExprVariable DontCare var

-- | Test pulling out two WaitFors that use the same variable:
testTransformWaitFor5 :: Test
testTransformWaitFor5 = TestCase $ testPass "testTransformWaitFor5" exp (transformWaitFor orig) (return ())
  where
    orig = A.Alt m True $ A.Several m [A.Only m $ A.AlternativeWait m A.WaitFor (exprVariable "t") (A.Skip m),
                                       A.Only m $ A.AlternativeWait m A.WaitFor (exprVariable "t") (A.Skip m)]
    exp = tag2 A.Seq DontCare $ mSpecP (tag3 A.Specification DontCare varName0 $ A.Declaration m A.Time Nothing) $
          mSpecP (tag3 A.Specification DontCare varName1 $ A.Declaration m A.Time Nothing) $
            mSeveralP
              [
                mOnlyP $ tag2 A.GetTime DontCare var0
                ,mOnlyP $ tag3 A.Assign DontCare [var0] $ tag2 A.ExpressionList DontCare [tag4 A.Dyadic DontCare A.Plus evar0 (exprVariablePattern "t")]
                ,mOnlyP $ tag2 A.GetTime DontCare var1
                ,mOnlyP $ tag3 A.Assign DontCare [var1] $ tag2 A.ExpressionList DontCare [tag4 A.Dyadic DontCare A.Plus evar1 (exprVariablePattern "t")]
                ,mOnlyP $ tag3 A.Alt DontCare True $ mSeveralA
                  [mOnlyA $ tag4 A.AlternativeWait DontCare A.WaitUntil evar0 (A.Skip m)
                  ,mOnlyA $ tag4 A.AlternativeWait DontCare A.WaitUntil evar1 (A.Skip m)]
              ]
    varName0 = (tag3 A.Name DontCare A.VariableName $ Named "nowt0" DontCare)
    var0 = tag2 A.Variable DontCare varName0
    evar0 = tag2 A.ExprVariable DontCare var0
    varName1 = (tag3 A.Name DontCare A.VariableName $ Named "nowt1" DontCare)
    var1 = tag2 A.Variable DontCare varName1
    evar1 = tag2 A.ExprVariable DontCare var1

testDeclareSizes :: Test
testDeclareSizes = TestList
  [
    testFoo 0 $ declFoo [4]
   ,testFoo 1 $ declFoo [4,5]
   ,testFoo 2 $ declFoo [4,5,6,7,8]
   
   ,testFoo 10 $ isChanArrFoo 1
   ,testFoo 11 $ isChanArrFoo 2
   ,testFoo 12 $ isChanArrFoo 3
   
{-   
   ,testFooDecl 10 [Nothing]
   ,testFooDecl 11 [Just 4, Nothing]
   ,testFooDecl 12 [Nothing, Nothing]  
   ,testFooDecl 13 [Nothing, Nothing, Nothing, Nothing]
   ,testFooDecl 14 [Nothing, Just 5, Just 6]
   ,testFooDecl 15 [Just 4, Nothing, Just 5, Nothing, Nothing]
-}   
   --TODO test that arrays that are abbreviations (Is and IsExpr) also get _sizes arrays, and that they are initialised correctly
   --TODO test records getting sizes arrays
   --TODO test reshapes/retypes abbreviations
  ]
  where
    -- spectype of foo, spectype of foo_sizes
    testFoo :: Int -> (A.SpecType, A.SpecType, State CompState ()) -> Test
    testFoo n (fooSpec, fooSizesSpec, st) = test n
      (strFoo $ strFooSizes term)
      (strFoo term) st (checkFooSizes fooSizesSpec)
      where
        strFoo = A.Spec emptyMeta (A.Specification emptyMeta (simpleName "foo") fooSpec)
        strFooSizes = A.Spec emptyMeta (A.Specification emptyMeta (simpleName "foo_sizes") fooSizesSpec)

    isChanArrFoo :: Int -> (A.SpecType, A.SpecType, State CompState ())
    isChanArrFoo n = (A.IsChannelArray emptyMeta (A.Array [A.Dimension n] $ A.Chan A.DirUnknown (A.ChanAttributes False False) A.Byte) (replicate n $ variable "c")
                     ,valFoo [n], return ())

    declFoo :: [Int] -> (A.SpecType, A.SpecType, State CompState ())
    declFoo ns = (A.Declaration emptyMeta t Nothing, valFoo ns, return ())
      where
        t = A.Array (map A.Dimension ns) A.Byte

    valFoo :: [Int] -> A.SpecType
    valFoo ds = A.IsExpr emptyMeta A.ValAbbrev (A.Array [A.Dimension $ length ds] A.Int) $ makeSizesLiteral ds

    makeSizesLiteral :: [Int] -> A.Expression
    makeSizesLiteral xs = A.Literal emptyMeta (A.Array [A.Dimension $ length xs] A.Int) $ A.ArrayLiteral emptyMeta $
      map (A.ArrayElemExpr . A.Literal emptyMeta A.Int . A.IntLiteral emptyMeta . show) xs
    
    checkFooSizes :: A.SpecType -> CompState -> Assertion
    checkFooSizes spec cs
      = do nd <- case Map.lookup "foo_sizes" (csNames cs) of
             Just nd -> return nd
             Nothing -> assertFailure "Could not find foo_sizes" >> return undefined
           assertEqual "ndName" "foo_sizes" (A.ndName nd)
           assertEqual "ndOrigName" "foo_sizes" (A.ndOrigName nd)
           assertEqual "ndType" spec (A.ndType nd)
           assertEqual "ndAbbrevMode" A.ValAbbrev (A.ndAbbrevMode nd)
  
    term = A.Only emptyMeta ()
    
    test :: Int -> A.Structured () -> A.Structured () -> State CompState () -> (CompState -> Assertion) -> Test
    test n exp inp st chk = TestLabel label $ TestCase $ testPassWithStateCheck label exp (declareSizesArray inp) st chk
      where
        label = "testDeclareSizes " ++ show n
---Returns the list of tests:
tests :: Test
tests = TestLabel "BackendPassesTest" $ TestList
 [
   testDeclareSizes
  ,testTransformWaitFor0
  ,testTransformWaitFor1
  ,testTransformWaitFor2
  ,testTransformWaitFor3
  ,testTransformWaitFor4
  ,testTransformWaitFor5
 ]


