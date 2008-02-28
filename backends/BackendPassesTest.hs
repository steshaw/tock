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
import Test.HUnit hiding (State)

import qualified AST as A
import BackendPasses
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


---Returns the list of tests:
tests :: Test
tests = TestLabel "BackendPassesTest" $ TestList
 [
   testTransformWaitFor0
  ,testTransformWaitFor1
  ,testTransformWaitFor2
  ,testTransformWaitFor3
  ,testTransformWaitFor4
  ,testTransformWaitFor5
 ]


