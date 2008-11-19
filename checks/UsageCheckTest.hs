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

import Control.Monad.Error
import Control.Monad.Reader
import Data.Graph.Inductive
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prelude hiding (fail)
import Test.HUnit

import qualified AST as A
import Check
import CompState
import Errors
import FlowGraph
import Metadata
import OccamEDSL
import TestFramework
import TestUtils hiding (Var)
import UsageCheckAlgorithms
import UsageCheckUtils
import Utils


--Shorthands for some variables to simplify the list of tests in this file
vA, vB, vC, vD :: A.Variable
vA = variable "a"
vB = A.DerefVariable emptyMeta $ variable "b"
vC = A.DirectedVariable emptyMeta A.DirInput $ variable "c"
vD = variable "d"
l0 :: A.Expression
l0 = intLiteral 0

tvA, tvB, tvC, tvD :: Var
tvA = Var $ vA
tvB = Var $ vB
tvC = Var $ vC
tvD = Var $ vD

m :: Meta
m = emptyMeta
   
--These are all shorthand for some useful "building block" processes
--The syntax is roughly: <variable list>_eq_<variable list>
--where a variable may be <letter> or <letter'subscript>
a_eq_0, a_eq_b, ab_eq_cd, ab_eq_ba, ab_eq_b0, a_eq_c_plus_d, a_eq_not_b :: A.Process
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
   tests :: [(Int,[Var],[Var],[Var],A.Process)]
   tests =
    [
--TODO test channel reads and writes (incl. reads in alts)
--TODO test process calls

     --Test assignments on non-sub variables:
      (0,[],[tvA],[],a_eq_0)
     ,(1,[tvB],[tvA],[],a_eq_b)
     ,(2,[tvC,tvD],[tvA,tvB],[],ab_eq_cd)
     ,(3,[tvA,tvB],[tvA,tvB],[],ab_eq_ba)
     ,(4,[tvB],[tvA,tvB],[],ab_eq_b0)
    
     --Test assignments and expressions:
     ,(200,[tvB],[tvA],[],a_eq_not_b)
     ,(201,[tvC,tvD],[tvA],[],a_eq_c_plus_d)
     
     -- Test simple outputs:
     ,(400,[tvA],[],[tvC],A.Output emptyMeta vC [A.OutExpression emptyMeta $ A.ExprVariable emptyMeta vA])
     ,(401,[tvA,tvB],[],[tvC],A.Output emptyMeta vC $ map ((A.OutExpression emptyMeta) . (A.ExprVariable emptyMeta)) [vA,vB])
     ,(402,[tvA,tvB],[],[tvC],A.Output emptyMeta vC
       [A.OutCounted emptyMeta (A.ExprVariable emptyMeta vA) (A.ExprVariable emptyMeta vB)])

     -- Test simple inputs:
     ,(500,[],[tvB],[tvC],A.Input emptyMeta vC (A.InputSimple emptyMeta [A.InVariable emptyMeta vB]))
     ,(501,[],[tvA,tvB],[tvC],A.Input emptyMeta vC
       (A.InputSimple emptyMeta [A.InVariable emptyMeta vB,A.InVariable emptyMeta vA]))
     ,(502,[],[tvA,tvB],[tvC],A.Input emptyMeta vC 
       (A.InputSimple emptyMeta [A.InCounted emptyMeta vA vB]))
    ]

   -- This is a custom test because there's no instance of Data for Vars.
   -- If we need to do this elsewhere, this could become a helper function in
   -- TestUtils.
   doTest :: (Int,[Var],[Var],[Var],A.Process) -> Test
   doTest (index, r, w, u, proc)
      = TestCase $ do result <- runPass' (getVarProc proc) startState
                      case result of
                        (_, Left err) ->
                          testFailure $ name ++ " failed: " ++ show err
                        (_, Right result) ->
                          assertEqual name (vars r (zip w $ repeat Nothing) u) (blankDef result)
    where
      name = "testGetVarProc" ++ show index
      blankDef :: Vars -> Vars
      blankDef (Vars r w u) = Vars r (Map.map (const Nothing) w) u

   startState :: CompState
   startState = emptyState

--TODO test declarations being recorded, when I've decided how to record them

type TestM = ReaderT CompState (Either String)
instance Die TestM where
  dieReport (_,s) = throwError s
instance Warn TestM where
  warnReport (_,_,s) = throwError s

buildTestFlowGraph :: [(Int, [Var], [Var])] -> [(Int, Int, EdgeLabel)] -> Int -> Int -> String -> FlowGraph TestM UsageLabel
buildTestFlowGraph ns es start end v
  = mkGraph
      ([(-1,makeTestNode emptyMeta $ Usage Nothing (Just $ ScopeIn False v) Nothing
        emptyVars),(-2,makeTestNode emptyMeta $ Usage Nothing (Just $ ScopeOut v) Nothing
          emptyVars)] ++ (map transNode ns))
      ([(-1,start,ESeq Nothing),(end,-2,ESeq Nothing)] ++ es)
  where
    transNode :: (Int, [Var], [Var]) -> (Int, FNode TestM UsageLabel)
    transNode (n,r,w) = (n,makeTestNode emptyMeta (Usage Nothing Nothing Nothing
      $ vars r (zip w $ repeat Nothing) []))

testInitVar :: Test
testInitVar = TestList
 [
   test "No variables" $ wrap $ oSEQ []
  ,test "One unused variable" $ wrap $ oSEQ [decl (return A.Int) oX []]
  ,test "One written-to variable" $ wrap $
    oSEQ [
      decl (return A.Int) oX [
        oX *:= return (3::Int)
      ]]
  ,test "One written-to then self-assigned variable" $ wrap $
    oSEQ [
      decl (return A.Int) oX [
        oX *:= return (3::Int)
        ,oX *:= oX
      ]]
  ,testWarn "One uninit self-assign" $ wrap $
    oSEQ [
      decl (return A.Int) oX [
        oX *:= oX
      ]]
  ,testWarn "One written-to variable, one uninit variable" $ wrap $
    oSEQ [
      decl (return A.Int) oX [
        decl (return A.Int) oY [
        oX *:= oY
      ]]]    
  ,test "Two parallel written-to variables, then another init" $ wrap $
    oSEQ [
      decl (return A.Int) oX [
        decl (return A.Int) oY [
          oPAR [
            oX *:= return (3::Int)
           ,oY *:= return (4::Int)
          ]
          ,decl (return A.Int) oZ [
            oZ *:= oX *+ oY
            ,oX *:= oZ
          ]
      ]]]

  ,test "Written to in all (two) IF guards, then self-assign" $ wrap $
    oSEQ [
      decl (return A.Int) oX [
        oIF [
          ifChoice (False, oX *:= return (3::Int))
          ,ifChoice (False, oX *:= return (4::Int))
        ]
      ]
      ,oX *:= oX
    ]
  ,testWarn "Written to in only one IF guards, then self-assign" $ wrap $
    oSEQ [
      decl (return A.Int) oX [
        oIF [
          ifChoice (False, oX *:= return (3::Int))
          ,ifChoice (False, oSKIP)
        ]
      ]
      ,oX *:= oX
    ]
  ,testWarn "Read from in last IF guards, then self-assign" $ wrap $
    oSEQ [
      decl (return A.Int) oX [
        oIF [
          ifChoice (False, oX *:= return (3::Int))
          ,ifChoice (oX, oX *:= return (4::Int))
        ]
      ]
      ,oX *:= oX
    ]

  ,test "Sandwiched loop" $ wrap $
    oSEQ [
      decl (return A.Int) oX [
        oX *:= (return (3::Int))
        ,oWHILE False oSKIP
        ,oX *:= oX
    ]]
  ,test "Read during loop, written before" $ wrap $
    oSEQ [
      decl (return A.Int) oX [
        oX *:= (return (3::Int))
        ,oWHILE False $ oX *:= oX
    ]]
  ,testWarn "Read during loop, not written before" $ wrap $
    oSEQ [
      decl (return A.Int) oX [
        oWHILE False $ oX *:= oX
    ]]
  ,testWarn "Written during loop, read after, not written before" $ wrap $
    oSEQ [
      decl (return A.Int) oX [
        oWHILE False $ oX *:= oX
        ,oX *:= oX
    ]]

  -- TODO test dereferenced variables

 ]
 where
   wrap x = oPROC "foo" [] x oempty

   test, testWarn :: String -> Occ A.AST -> Test
   test name x = testOccamPassWarn ("checkInitVar " ++ name) null x checkInitVarPass
   testWarn name x = testOccamPassWarn ("checkInitVar " ++ name) (not . null) x checkInitVarPass
   

{-
testReachDef :: Test
testReachDef = TestList
 [
  -- Nothing written/read, blank results:
   test 0 [(0,[],[])] [] []  
  -- Written but not read, no results:
  ,test 1 [(0,[],[variable "x"])] [] []
  -- Written then read, no branching
  ,test 2 [(0,[],[variable "x"]),(1,[variable "x"],[])] [(0,1,ESeq)] [(1,[0])]
  ,test 3 [(0,[],[variable "x"]),(1,[],[]),(2,[variable "x"],[])] [(0,1,ESeq),(1,2,ESeq)] [(2,[0])]
  ,test 4 [(0,[],[variable "x"]),(1,[],[variable "x"]),(2,[variable "x"],[])] [(0,1,ESeq),(1,2,ESeq)] [(2,[1])]
  
  -- Lattice, written in 0, read in 3:
  ,test 100 [(0,[],[variable "x"]),(1,[],[]),(2,[],[]),(3,[variable "x"],[])] latEdges [(3,[0])]
  -- Lattice, written in 0, read in 1,2 and 3:
  ,test 101 [(0,[],[variable "x"]),(1,[variable "x"],[]),(2,[variable "x"],[]),(3,[variable "x"],[])] latEdges [(3,[0]),(1,[0]),(2,[0])]
  -- Lattice, written 0, 1 and 2, read in 3:
  ,test 102 [(0,[],[variable "x"]),(1,[],[variable "x"]),(2,[],[variable "x"]),(3,[variable "x"],[])] latEdges [(3,[1,2])]
  -- Lattice written in 0 and 1, read in 2 and 3:
  ,test 103 [(0,[],[variable "x"]),(1,[],[variable "x"]),(2,[variable "x"],[]),(3,[variable "x"],[])] latEdges [(3,[0,1]),(2,[0])]
  
  --Loops:
  
  -- Written before loop, read afterwards:
  ,test 200 [(0,[],[variable "x"]),(1,[],[]),(2,[],[]),(3,[],[]),(4,[variable "x"],[])] loopEdges [(4,[0])]
  -- Written before loop, read during:
  ,test 201 [(0,[],[variable "x"]),(1,[],[]),(2,[variable "x"],[]),(3,[],[]),(4,[],[])] loopEdges [(2,[0])]
  -- Written before loop, written then read during:
  ,test 202 [(0,[],[variable "x"]),(1,[],[]),(2,[],[variable "x"]),(3,[variable "x"],[]),(4,[],[])] loopEdges [(3,[2])]
  -- Written before loop, written then read during, and read after:
  ,test 203 [(0,[],[variable "x"]),(1,[],[]),(2,[],[variable "x"]),(3,[variable "x"],[]),(4,[variable "x"],[])] loopEdges [(3,[2]),(4,[0,2])]
  
  --TODO test derefenced variables
 ]
 where
   latEdges :: [(Int,Int,EdgeLabel)]
   latEdges = [(0,1,ESeq),(0,2,ESeq),(1,3,ESeq),(2,3,ESeq)]
   
   loopEdges :: [(Int,Int,EdgeLabel)]
   loopEdges = [(0,1,ESeq),(1,2,ESeq),(2,3,ESeq),(3,1,ESeq),(1,4,ESeq)]   
   
   -- It is implied that 0 is the start, and the highest node number is the end, and the var is "x"
   test :: Int -> [(Int,[A.Variable],[A.Variable])] -> [(Int,Int,EdgeLabel)] -> [(Int,[Int])] -> Test
   test testNum ns es expMap = TestCase $ assertEither ("testReachDef " ++ show testNum) (Map.fromList $ map (transformPair id ((Map.singleton $ Var $ variable "x") . Set.fromList)) expMap) $
     findReachDef (buildTestFlowGraph (map (transformTriple id (map Var) (map Var)) ns) es 0 (maximum $ map fst3 ns) "x") (-1)
  
   fst3 :: (a,b,c) -> a
   fst3(x,_,_) = x
-}
tests :: Test
tests = TestLabel "RainUsageCheckTest" $ TestList
 [
  testGetVarProc
  ,testInitVar
--  ,testReachDef
 ]
