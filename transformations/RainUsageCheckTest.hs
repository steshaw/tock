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

module RainUsageCheckTest (tests) where

import Prelude hiding (fail)
import Test.HUnit


import qualified AST as A
import Metadata
import TestUtil
import RainUsageCheck


--Shorthands for some variables to simplify the list of tests in this file
vA = variable "a"
vB = A.DerefVariable emptyMeta $ variable "b"
vC = A.DirectedVariable emptyMeta A.DirInput $ variable "c"
vD = variable "d"
vL = variable "l"
l0 = intLiteral 0
l1 = intLiteral 1

tvA = Plain "a"
tvB = Deref "b"
tvC = Dir A.DirInput "c"
tvD = Plain "d"
tvL = Plain "l"
   
--These are all shorthand for some useful "building block" processes
--The syntax is roughly: <variable list>_eq_<variable list>
--where a variable may be <letter> or <letter'subscript>
a_eq_0 = A.Assign m [vA] $ A.ExpressionList m [l0]
a_eq_b = A.Assign emptyMeta [vA] $ A.ExpressionList emptyMeta [A.ExprVariable emptyMeta vB]
ab_eq_cd = A.Assign m [vA,vB] $ A.ExpressionList m [A.ExprVariable m vC,A.ExprVariable m vD]
ab_eq_ba = A.Assign m [vA,vB] $ A.ExpressionList m [A.ExprVariable m vA,A.ExprVariable m vB]
ab_eq_b0 = A.Assign m [vA,vB] $ A.ExpressionList m [A.ExprVariable m vB,l0]
   
a_eq_c_plus_d = A.Assign m [vA] $ A.ExpressionList m [A.Dyadic m A.Plus (A.ExprVariable m vC) (A.ExprVariable m vD)]
a_eq_not_b = A.Assign m [vA] $ A.ExpressionList m [A.Monadic m A.MonadicNot (A.ExprVariable m vB)]



testGetVarProc :: Test
testGetVarProc = TestList (map doTest tests)
 where
   tests =
    [
--TODO test channel reads and writes (incl. reads in alts)
--TODO test process calls
--TODO test function calls

     --Test assignments on non-sub variables:
      (0,[],[tvA],[tvA],[],a_eq_0)
     ,(1,[tvB],[tvA],[tvA],[],a_eq_b)
     ,(2,[tvC,tvD],[tvA,tvB],[tvA,tvB],[],ab_eq_cd)
     ,(3,[tvA,tvB],[tvA,tvB],[tvA,tvB],[],ab_eq_ba)
     ,(4,[tvB],[tvA,tvB],[tvA,tvB],[],ab_eq_b0)
    
     --Test assignments and expressions:
     ,(200,[tvB],[tvA],[tvA],[],a_eq_not_b)
     ,(201,[tvC,tvD],[tvA],[tvA],[],a_eq_c_plus_d)
     
     -- Test time statements:
     ,(300,[],[tvB],[tvB],[],A.GetTime emptyMeta vB)
     ,(301,[tvA],[],[],[],A.Wait emptyMeta A.WaitFor $ A.ExprVariable emptyMeta vA)
     
     -- Test simple outputs:
     ,(400,[tvA],[],[],[tvC],A.Output emptyMeta vC [A.OutExpression emptyMeta $ A.ExprVariable emptyMeta vA])
     ,(401,[tvA,tvB],[],[],[tvC],A.Output emptyMeta vC $ map ((A.OutExpression emptyMeta) . (A.ExprVariable emptyMeta)) [vA,vB])
     ,(402,[tvA,tvB],[],[],[tvC],A.Output emptyMeta vC
       [A.OutCounted emptyMeta (A.ExprVariable emptyMeta vA) (A.ExprVariable emptyMeta vB)])

     -- Test simple inputs:
     ,(500,[],[tvB],[tvB],[tvC],A.Input emptyMeta vC (A.InputSimple emptyMeta [A.InVariable emptyMeta vB]))
     ,(501,[],[tvA,tvB],[tvA,tvB],[tvC],A.Input emptyMeta vC
       (A.InputSimple emptyMeta [A.InVariable emptyMeta vB,A.InVariable emptyMeta vA]))
     ,(502,[],[tvA,tvB],[tvA,tvB],[tvC],A.Input emptyMeta vC 
       (A.InputSimple emptyMeta [A.InCounted emptyMeta vA vB]))
    ]
   doTest :: (Int,[Var],[Var],[Var],[Var],A.Process) -> Test
   doTest (index,mr,mw,dw,u,proc) = TestCase $ assertEqual ("testGetVarProc-" ++ (show index)) (vars mr mw dw u) (getVarProc proc)
  
{- 
testParUsageCheck :: Test
testParUsageCheck = TestList (map doTest tests)
 where
  tests =
   [
      (0,makePar [a_eq_0,a_eq_b],Just [makePar [a_eq_0,a_eq_b]])
     ,(1,makeSeq [a_eq_0,a_eq_b],Nothing)
     ,(2,makePar [a_eq_b,c_eq_d],Nothing)
     ,(3,makePar [a_eq_b,c_eq_b],Nothing)
     ,(4,makeSeq [makePar [a_eq_0,a_eq_b],makePar [c_eq_b,c_eq_d]],Just [makePar [a_eq_0,a_eq_b],makePar [c_eq_b,c_eq_d]])
     ,(5,makePar [makePar [a_eq_0,a_eq_b],makePar [c_eq_b,c_eq_d]],Just [makePar [a_eq_0,a_eq_b],makePar [c_eq_b,c_eq_d]])
     ,(6,makePar [makeSeq [a_eq_0,c_eq_d],c_eq_b],Just [makePar [makeSeq [a_eq_0,c_eq_d],c_eq_b]])
     ,(7,makePar [makeSeq [a_eq_0,a_eq_b],c_eq_b],Nothing)

     --Replicated PARs:
     --TODO change this to par each loops:
     
     ,(300,makeRepPar a_eq_0,Just [makeRepPar a_eq_0])
     ,(301,makeRepPar $ makeSeq [a_eq_0],Just [makeRepPar $ makeSeq [a_eq_0]])
     ,(302,makeRepPar $ makePar [a_eq_0],Just [makeRepPar $ makePar [a_eq_0]])

   ]
  doTest :: (Int,A.Process,Maybe [A.Process]) -> Test
  doTest (index,proc,exp) = TestCase $ assertEqual ("testParUsageCheck-" ++ (show index)) exp (UC.parUsageCheck proc)
-}

--TODO add tests for initialising a variable before use.
--TODO especially test things like only initialising the variable in one part of an if

tests :: Test
tests = TestList
 [
  testGetVarProc
--  ,testParUsageCheck
 ]



