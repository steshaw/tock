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

module UsageCheckTest (tests) where

import Prelude hiding (fail)
import Test.HUnit


import qualified AST as A
import TestUtil
import qualified UsageCheck as UC


--See note in UsageCheck about WrittenRead not using sets.  Therefore our equality function is inefficient
--(it is an O(N^2) comparison), but thankfully it's only used during testing:
assertEqualWR :: String -> UC.WrittenRead -> UC.WrittenRead -> Assertion
assertEqualWR text exp act 
  = assertCompareCustom text inefficientEqual exp act
  where
    --We can assume there are no duplicates, because getVars will remove duplicates, and
    --our expected values in tests should not have duplicate entries
    inefficientEqual :: UC.WrittenRead -> UC.WrittenRead -> Bool
    inefficientEqual (w0,r0) (w1,r1) = 
      ((length w0) == (length w1)) && ((length r0) == (length r1)) &&
      (allIn w0 w1) && (allIn r0 r1) 
      where
        --checks that all elements of the first list are in the second list:
        allIn :: Eq a => [a] -> [a] -> Bool
        allIn [] _ = True
        allIn (x:xs) list = (elem x list) && (allIn xs list)

--Shorthands for some variables to simplify the list of tests in this file
vA = variable "a"
vB = variable "b"
vC = variable "c"
vD = variable "d"
l0 = intLiteral 0
l1 = intLiteral 1
vA_0 = A.SubscriptedVariable m (A.Subscript m l0) vA
vA_1 = A.SubscriptedVariable m (A.Subscript m l1) vA
vA_B = A.SubscriptedVariable m (A.Subscript m (A.ExprVariable m vB)) vA
vC_D = A.SubscriptedVariable m (A.Subscript m (A.ExprVariable m vD)) vC
vA_BpC = A.SubscriptedVariable m (A.Subscript m (A.Dyadic m A.Plus (A.ExprVariable m vB) (A.ExprVariable m vC))) vA
vA_i = A.SubscriptedVariable m (A.Subscript m (A.ExprVariable m (variable "i"))) vA
   
--These are all shorthand for some useful "building block" processes
--The syntax is roughly: <variable list>_eq_<variable list>
--where a variable may be <letter> or <letter'subscript>
a_eq_0 = A.Assign m [vA] $ A.ExpressionList m [l0]
a_eq_b = makeSimpleAssign "a" "b"
b_eq_c = makeSimpleAssign "b" "c"
c_eq_b = makeSimpleAssign "c" "b"
c_eq_d = makeSimpleAssign "c" "d"
ab_eq_cd = A.Assign m [vA,vB] $ A.ExpressionList m [A.ExprVariable m vC,A.ExprVariable m vD]
ab_eq_ba = A.Assign m [vA,vB] $ A.ExpressionList m [A.ExprVariable m vA,A.ExprVariable m vB]
ab_eq_b0 = A.Assign m [vA,vB] $ A.ExpressionList m [A.ExprVariable m vB,l0]
a'b_eq_c = A.Assign m [vA_B] $ A.ExpressionList m [A.ExprVariable m vC]
a'b_eq_c'd = A.Assign m [vA_B] $ A.ExpressionList m [A.ExprVariable m vC_D]
a'b_eq_0 = A.Assign m [vA_B] $ A.ExpressionList m [l0]
a'0_eq_0 = A.Assign m [vA_0] $ A.ExpressionList m [l0]
a'1_eq_0 = A.Assign m [vA_1] $ A.ExpressionList m [l0]
a'0_eq_c = A.Assign m [vA_0] $ A.ExpressionList m [A.ExprVariable m vC]
a'i_eq_0 = A.Assign m [vA_i] $ A.ExpressionList m [l0]
   
a_eq_c_plus_d = A.Assign m [vA] $ A.ExpressionList m [A.Dyadic m A.Plus (A.ExprVariable m vC) (A.ExprVariable m vD)]
a_eq_not_b = A.Assign m [vA] $ A.ExpressionList m [A.Monadic m A.MonadicNot (A.ExprVariable m vB)]
a'b_plus_c_eq_d = A.Assign m [vA_BpC] $ A.ExpressionList m [A.ExprVariable m vD]



testGetVar :: Test
testGetVar = TestList (map doTest tests)
 where
   tests =
    [
--TODO test channel reads and writes (incl. reads in alts)
--TODO test process calls
--TODO test function calls
--TODO test if/case/while

     --Test assignments on non-sub variables:
      (0,[vA],[],a_eq_0)
     ,(1,[vA],[vB],a_eq_b)
     ,(2,[vA,vB],[vC,vD],ab_eq_cd)
     ,(3,[vA,vB],[vA,vB],ab_eq_ba)
     ,(4,[vA,vB],[vB],ab_eq_b0)
     ,(5,[vA,vC],[vB,vD],makeSeq [a_eq_b,c_eq_d])
     ,(6,[vA,vC],[vB,vD],makePar [a_eq_b,c_eq_d])
     ,(7,[vA,vC],[vD],makeSeq [a_eq_0,c_eq_d])
     ,(8,[vA,vC],[vD],makePar [a_eq_0,c_eq_d])
    
     --Test assignments on sub variables:
     ,(100,[vA_0],[],a'0_eq_0)
     ,(101,[vA_0],[vC],a'0_eq_c)
     ,(101,[vA_B],[vB],a'b_eq_0)
     ,(102,[vA_B],[vB,vC],a'b_eq_c)
     ,(103,[vA_B,vC],[vB,vD],makeSeq [a'b_eq_0,c_eq_d])
     ,(104,[vA_B,vC],[vB,vD],makePar [a'b_eq_0,c_eq_d])
     ,(105,[vA_B],[vB,vC_D,vD],a'b_eq_c'd)
     
     --Test assignments and expressions:
     ,(200,[vA],[vB],a_eq_not_b)
     ,(201,[vA],[vC,vD],a_eq_c_plus_d)
     
     --Test expressions in subscripts:     
     ,(300,[vA_BpC],[vB,vC,vD],a'b_plus_c_eq_d)
     

     
    ]
   doTest :: (Int,[A.Variable],[A.Variable],A.Process) -> Test
   doTest (index,written,read,proc) = TestCase $ assertEqualWR ("testGetVar-" ++ (show index)) (written,read) (UC.getVars proc)   
   
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
     ,(8,makePar [a'b_eq_0,b_eq_c],Just [makePar [a'b_eq_0,b_eq_c]])

     --Different (some constant,some not) indexes:
     --The parUsageCheck assumes that constant folding has been run on the code, so any remaining variable/symbol
     --must be non-constant:
     
     ,(100,makePar[a'0_eq_0,a'1_eq_0],Nothing)
     ,(101,makePar[a'0_eq_0,a'b_eq_0],Just [makePar[a'0_eq_0,a'b_eq_0]])
     ,(102,makePar[a'b_eq_0,a'b_eq_0],Just [makePar[a'b_eq_0,a'b_eq_0]])
     ,(103,makePar[a'b_eq_0,a'b_plus_c_eq_d],Just [makePar[a'b_eq_0,a'b_plus_c_eq_d]])
     ,(104,makePar[a'0_eq_0,a'b_plus_c_eq_d],Just [makePar[a'0_eq_0,a'b_plus_c_eq_d]])
     
     ,(110,makePar[makeSeq[a'0_eq_0,a'b_eq_0],c_eq_b],Nothing)
     ,(111,makePar[makeSeq[a'0_eq_0,a'b_eq_0],a'1_eq_0],Just [makePar[makeSeq[a'0_eq_0,a'b_eq_0],a'1_eq_0]])

     --Replicated PARs:
     
     ,(300,makeRepPar a_eq_0,Just [makeRepPar a_eq_0])
     ,(301,makeRepPar $ makeSeq [a_eq_0],Just [makeRepPar $ makeSeq [a_eq_0]])
     ,(302,makeRepPar $ makePar [a_eq_0],Just [makeRepPar $ makePar [a_eq_0]])
     ,(303,makeRepPar  a'i_eq_0,Nothing)
     ,(303,makeRepPar $ makeSeq [a'i_eq_0],Nothing)
     ,(303,makeRepPar $ makePar [a'i_eq_0],Nothing)

   ]
  doTest :: (Int,A.Process,Maybe [A.Process]) -> Test
  doTest (index,proc,exp) = TestCase $ assertEqual ("testParUsageCheck-" ++ (show index)) exp (UC.parUsageCheck proc)
  

tests :: Test
tests = TestList
 [
  testGetVar
  ,testParUsageCheck
 ]



