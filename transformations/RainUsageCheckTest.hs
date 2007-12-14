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

module RainUsageCheckTest (qcTests) where

import Control.Monad.Identity
import Data.Graph.Inductive
import Data.Array.IArray
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Prelude hiding (fail)
import Test.HUnit
import Test.QuickCheck


import ArrayUsageCheck
import qualified AST as A
import FlowGraph
import Metadata
import PrettyShow
import RainUsageCheck
import TestUtils
import Utils


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

--TODO test declarations being recorded, when I've decided how to record them

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

buildTestFlowGraph :: [(Int, [Var], [Var], [Var])] -> [(Int, Int, EdgeLabel)] -> Int -> Int -> String -> FlowGraph Identity (Maybe Decl, Vars)
buildTestFlowGraph ns es start end v
  = mkGraph
      ([(-1,Node (emptyMeta,(Just $ ScopeIn v, emptyVars), undefined)),(-2,Node (emptyMeta,(Just $ ScopeOut v,emptyVars), undefined))] ++ (map transNode ns))
      ([(-1,start,ESeq),(end,-2,ESeq)] ++ es)
  where
    transNode :: (Int, [Var], [Var], [Var]) -> (Int, FNode Identity (Maybe Decl, Vars))
    transNode (n,mr,mw,dw) = (n,Node (emptyMeta, (Nothing,vars mr mw dw []), undefined))

testInitVar :: Test
testInitVar = TestList
 [
   -- Single node, x not touched
   testInitVarPass 0 [(0,[],[],[])] [] 0 0 "x"
   -- Single node, x written to
  ,testInitVarPass 1 [(0,[],[],[Plain "x"])] [] 0 0 "x"
   -- Single node, x read from (FAIL)
  ,testInitVarFail 2 [(0,[Plain "x"],[],[])] [] 0 0 "x"
   -- Single node, x read from and written to (FAIL - x must be written to before the read.  
   --   This line is akin to x = x + 1, so x must be written to beforehand)
  ,testInitVarFail 3 [(0,[Plain "x"],[],[Plain "x"])] [] 0 0 "x"
  
  -- Two nodes, x written to then read
  ,testInitVarPass 10 [(0,[],[],[Plain "x"]), (1,[Plain "x"],[],[])] [(0,1,ESeq)] 0 1 "x"
  -- Two nodes, x read then written to (FAIL)
  ,testInitVarFail 11 [(0,[],[],[Plain "x"]), (1,[Plain "x"],[],[])] [(1,0,ESeq)] 1 0 "x"
  -- Two nodes, x maybe-written to then read (FAIL)
  ,testInitVarFail 12 [(0,[],[Plain "x"],[]), (1,[Plain "x"],[],[])] [(0,1,ESeq)] 0 1 "x"
  -- As test 10 (x written to then read) but using the par edges.
  ,testInitVarPass 13 [(0,[],[],[Plain "x"]), (1,[Plain "x"],[],[])] [(0,1,EStartPar 0)] 0 1 "x"
  ,testInitVarPass 14 [(0,[],[],[Plain "x"]), (1,[Plain "x"],[],[])] [(0,1,EEndPar 0)] 0 1 "x"

  -- Diamond tests (0 branches to 1 and 2, which both merge to 3):
  -- x written to in 0 and 1, then read in 3
  ,testInitVarPass 20 [(0,[],[],[]),(1,[],[],[Plain "x"]), (2,[],[],[Plain "x"]), (3,[Plain "x"],[],[])]
    [(0,1,ESeq),(0,2,ESeq),(1,3,ESeq),(2,3,ESeq)] 0 3 "x"
  -- x written to only in 2 then read in 3 (FAIL)
  ,testInitVarFail 21 [(0,[],[],[]),(1,[],[],[]), (2,[],[],[Plain "x"]), (3,[Plain "x"],[],[])]
    [(0,1,ESeq),(0,2,ESeq),(1,3,ESeq),(2,3,ESeq)] 0 3 "x"
  -- x definitely written to in 2, but not 1 (FAIL)
  ,testInitVarFail 22 [(0,[],[],[]),(1,[],[Plain "x"],[]), (2,[],[],[Plain "x"]), (3,[Plain "x"],[],[])]
    [(0,1,ESeq),(0,2,ESeq),(1,3,ESeq),(2,3,ESeq)] 0 3 "x"
  -- like test 21, but the link missing from 1 to 3, so test will pass
  ,testInitVarPass 23 [(0,[],[],[]),(1,[],[],[]), (2,[],[],[Plain "x"]), (3,[Plain "x"],[],[])]
    [(0,1,ESeq),(0,2,ESeq),(2,3,ESeq)] 0 3 "x"
  -- variable written to in 0, read in 3
  ,testInitVarPass 24 [(0,[],[],[Plain "x"]),(1,[],[],[]), (2,[],[],[]), (3,[Plain "x"],[],[])]
    [(0,1,ESeq),(0,2,ESeq),(1,3,ESeq),(2,3,ESeq)] 0 3 "x"
  -- variable never written to, but read in 3
  ,testInitVarFail 25 [(0,[],[],[]),(1,[],[],[]), (2,[],[],[]), (3,[Plain "x"],[],[])]
    [(0,1,ESeq),(0,2,ESeq),(1,3,ESeq),(2,3,ESeq)] 0 3 "x"
  -- variable written to in 2 and 3, but read in 1 (FAIL):
  ,testInitVarFail 26 [(0,[],[],[]),(1,[Plain "x"],[],[]), (2,[],[],[Plain "x"]), (3,[],[],[Plain "x"])]
    [(0,1,ESeq),(0,2,ESeq),(1,3,ESeq),(2,3,ESeq)] 0 3 "x"

  -- Test parallel diamonds:
  -- written to in 1 and 2, read in 3
  -- This would fail CREW, but that's not what we're testing here:
  ,testInitVarPass 30 [(0,[],[],[]),(1,[],[],[Plain "x"]), (2,[],[],[Plain "x"]), (3,[Plain "x"],[],[])]
    [(0,1,EStartPar 0),(0,2,EStartPar 0),(1,3,EEndPar 0),(2,3,EEndPar 0)] 0 3 "x"
  -- written to in 1, read in 3
  ,testInitVarPass 31 [(0,[],[],[]),(1,[],[],[Plain "x"]), (2,[],[],[]), (3,[Plain "x"],[],[])]
    [(0,1,EStartPar 0),(0,2,EStartPar 0),(1,3,EEndPar 0),(2,3,EEndPar 0)] 0 3 "x"
  -- written to in 0, read in 3
  ,testInitVarPass 32 [(0,[],[],[Plain "x"]),(1,[],[],[]), (2,[],[],[]), (3,[Plain "x"],[],[])]
    [(0,1,EStartPar 0),(0,2,EStartPar 0),(1,3,EEndPar 0),(2,3,EEndPar 0)] 0 3 "x"
  -- never written to, but read in 3:
  ,testInitVarFail 33 [(0,[],[],[]),(1,[],[],[]), (2,[],[],[]), (3,[Plain "x"],[],[])]
    [(0,1,EStartPar 0),(0,2,EStartPar 0),(1,3,EEndPar 0),(2,3,EEndPar 0)] 0 3 "x"
  -- written to in 1, read in 2 (again, would fail CREW) (FAIL):
  ,testInitVarFail 34 [(0,[],[],[]),(1,[],[],[Plain "x"]), (2,[Plain "x"],[],[]), (3,[],[],[])]
    [(0,1,EStartPar 0),(0,2,EStartPar 0),(1,3,EEndPar 0),(2,3,EEndPar 0)] 0 3 "x"
  -- written to in 1, read in 2 and 3 (again, would fail CREW) (FAIL):
  ,testInitVarFail 35 [(0,[],[],[]),(1,[],[],[Plain "x"]), (2,[Plain "x"],[],[]), (3,[Plain "x"],[],[])]
    [(0,1,EStartPar 0),(0,2,EStartPar 0),(1,3,EEndPar 0),(2,3,EEndPar 0)] 0 3 "x"

  
  -- Test loops (0 -> 1, 1 -> 2 -> 3 -> 1, 1 -> 4)
  -- Loop, nothing happens:
  ,testInitVarPass 100 [(0,[],[],[]),(1,[],[],[]),(2,[],[],[]),(3,[],[],[]),(4,[],[],[])]
    [(0,1,ESeq), (1,2,ESeq), (2,3,ESeq), (3,1,ESeq), (1,4,ESeq)] 0 4 "x"
  -- Loop, written to before the loop, read afterwards:
  ,testInitVarPass 101 [(0,[],[],[Plain "x"]),(1,[],[],[]),(2,[],[],[]),(3,[],[],[]),(4,[Plain "x"],[],[])]
    [(0,1,ESeq), (1,2,ESeq), (2,3,ESeq), (3,1,ESeq), (1,4,ESeq)] 0 4 "x"
  -- Loop, written to before the loop, read during the loop
  ,testInitVarPass 102 [(0,[],[],[Plain "x"]),(1,[],[],[]),(2,[],[],[]),(3,[Plain "x"],[],[]),(4,[],[],[])]
    [(0,1,ESeq), (1,2,ESeq), (2,3,ESeq), (3,1,ESeq), (1,4,ESeq)] 0 4 "x"
  -- Loop, written to during the loop, read afterwards (FAIL - loop might not be executed)
  ,testInitVarFail 103 [(0,[],[],[]),(1,[],[],[]),(2,[],[],[Plain "x"]),(3,[],[],[]),(4,[Plain "x"],[],[])]
    [(0,1,ESeq), (1,2,ESeq), (2,3,ESeq), (3,1,ESeq), (1,4,ESeq)] 0 4 "x"
  -- Loop, written to and then read during the loop:
  ,testInitVarPass 104 [(0,[],[],[]),(1,[],[],[]),(2,[],[],[Plain "x"]),(3,[Plain "x"],[],[]),(4,[],[],[])]
    [(0,1,ESeq), (1,2,ESeq), (2,3,ESeq), (3,1,ESeq), (1,4,ESeq)] 0 4 "x"
  -- Loop, read then written to during the loop (FAIL):    
  ,testInitVarFail 105 [(0,[],[],[]),(1,[],[],[]),(2,[Plain "x"],[],[]),(3,[],[],[Plain "x"]),(4,[],[],[])]
    [(0,1,ESeq), (1,2,ESeq), (2,3,ESeq), (3,1,ESeq), (1,4,ESeq)] 0 4 "x"
    
  -- TODO work out (and test) par loops
  -- TODO test dereferenced variables
 ]
 where
   testInitVarPass :: Int -> [(Int, [Var], [Var], [Var])] -> [(Int, Int, EdgeLabel)] -> Int -> Int -> String -> Test
   testInitVarPass testNum ns es start end v = TestCase $ assertEither ("testInitVar " ++ show testNum) () $ checkInitVar (buildTestFlowGraph ns es start end v) (-1)
   
   testInitVarFail :: Int -> [(Int, [Var], [Var], [Var])] -> [(Int, Int, EdgeLabel)] -> Int -> Int -> String -> Test
   testInitVarFail testNum ns es start end v = TestCase $ assertEitherFail ("testInitVar " ++ show testNum) $ checkInitVar (buildTestFlowGraph ns es start end v) (-1)

testReachDef :: Test
testReachDef = TestList
 [
  -- Nothing written/read, blank results:
   test 0 [(0,[],[])] [] []  
  -- Written but not read, no results:
  ,test 1 [(0,[],[Plain "x"])] [] []
  -- Written then read, no branching
  ,test 2 [(0,[],[Plain "x"]),(1,[Plain "x"],[])] [(0,1,ESeq)] [(1,[0])]
  ,test 3 [(0,[],[Plain "x"]),(1,[],[]),(2,[Plain "x"],[])] [(0,1,ESeq),(1,2,ESeq)] [(2,[0])]
  ,test 4 [(0,[],[Plain "x"]),(1,[],[Plain "x"]),(2,[Plain "x"],[])] [(0,1,ESeq),(1,2,ESeq)] [(2,[1])]
  
  -- Lattice, written in 0, read in 3:
  ,test 100 [(0,[],[Plain "x"]),(1,[],[]),(2,[],[]),(3,[Plain "x"],[])] latEdges [(3,[0])]
  -- Lattice, written in 0, read in 1,2 and 3:
  ,test 101 [(0,[],[Plain "x"]),(1,[Plain "x"],[]),(2,[Plain "x"],[]),(3,[Plain "x"],[])] latEdges [(3,[0]),(1,[0]),(2,[0])]
  -- Lattice, written 0, 1 and 2, read in 3:
  ,test 102 [(0,[],[Plain "x"]),(1,[],[Plain "x"]),(2,[],[Plain "x"]),(3,[Plain "x"],[])] latEdges [(3,[1,2])]
  -- Lattice written in 0 and 1, read in 2 and 3:
  ,test 103 [(0,[],[Plain "x"]),(1,[],[Plain "x"]),(2,[Plain "x"],[]),(3,[Plain "x"],[])] latEdges [(3,[0,1]),(2,[0])]
  
  --Loops:
  
  -- Written before loop, read afterwards:
  ,test 200 [(0,[],[Plain "x"]),(1,[],[]),(2,[],[]),(3,[],[]),(4,[Plain "x"],[])] loopEdges [(4,[0])]
  -- Written before loop, read during:
  ,test 201 [(0,[],[Plain "x"]),(1,[],[]),(2,[Plain "x"],[]),(3,[],[]),(4,[],[])] loopEdges [(2,[0])]
  -- Written before loop, written then read during:
  ,test 202 [(0,[],[Plain "x"]),(1,[],[]),(2,[],[Plain "x"]),(3,[Plain "x"],[]),(4,[],[])] loopEdges [(3,[2])]
  -- Written before loop, written then read during, and read after:
  ,test 203 [(0,[],[Plain "x"]),(1,[],[]),(2,[],[Plain "x"]),(3,[Plain "x"],[]),(4,[Plain "x"],[])] loopEdges [(3,[2]),(4,[0,2])]
  
  --TODO test derefenced variables
 ]
 where
   latEdges :: [(Int,Int,EdgeLabel)]
   latEdges = [(0,1,ESeq),(0,2,ESeq),(1,3,ESeq),(2,3,ESeq)]
   
   loopEdges :: [(Int,Int,EdgeLabel)]
   loopEdges = [(0,1,ESeq),(1,2,ESeq),(2,3,ESeq),(3,1,ESeq),(1,4,ESeq)]   
   
   blankMW :: (Int,[Var],[Var]) -> (Int, [Var], [Var], [Var])
   blankMW (n,mr,dw) = (n,mr,[],dw)
 
   -- It is implied that 0 is the start, and the highest node number is the end, and the var is "x"
   test :: Int -> [(Int,[Var],[Var])] -> [(Int,Int,EdgeLabel)] -> [(Int,[Int])] -> Test
   test testNum ns es expMap = TestCase $ assertEither ("testReachDef " ++ show testNum) (Map.fromList $ map (transformPair id ((Map.singleton $ Plain "x") . Set.fromList)) expMap) $
     findReachDef (buildTestFlowGraph (map blankMW ns) es 0 (maximum $ map fst3 ns) "x") (-1)
  
   fst3 :: (a,b,c) -> a
   fst3(x,_,_) = x

testArrayCheck :: Test
testArrayCheck = TestList
  [
   -- x_1 = 0
   pass (0, [], [[0,1]], [])
   -- x_1 = 0, 3x_1 >= 0 --> 0 >= 0
  ,pass (1, [[0,0]], [[0,1]], [[0,3]])
   -- -7 + x_1 = 0
  ,pass (2, [], [[-7,1]], [])
   -- x_1 = 9, 3 + 2x_1 >= 0  -->  21 >= 0
  ,pass (3, [[21,0]], [[-9,1]], [[3,2]])
   -- x_1 + x_2 = 0, 4x_1 = 8, 2x_2 = -4
  ,pass (4, [], [[0,1,1], [-8,4,0], [4,0,2]], [])
   -- - x_1 + x_2 = 0, 4x_1 = 8, 2x_2 = 4
  ,pass (5, [], [[0,-1,1], [-8,4,0], [-4,0,2]], [])
   -- -x_1 = -9, 3 + 2x_1 >= 0  -->  21 >= 0
  ,pass (6, [[21,0]], [[9,-1]], [[3,2]])


   -- From the Omega Test paper (x = x_1, y = x_2, z = x_3, sigma = x_1 (effectively)):
  ,pass (100, [[11,13,0,0], [28,-13,0,0], [47,-5,0,0], [53,5,0,0]], [[-17,7,12,31], [-7,3,5,14]],
    [[-1,1,0,0], [40,-1,0,0], [50,0,1,0], [50,0,-1,0]])
  
  -- Impossible/inconsistent equality constraints:
  
   -- -7 = 0
  ,TestCase $ assertEqual "testArrayCheck 1002" (Nothing) (solveConstraints [simpleArray [(0,7),(1,0)]] [])
   -- x_1 = 3, x_1 = 4
  ,TestCase $ assertEqual "testArrayCheck 1003" (Nothing) (solveConstraints [simpleArray [(0,-3),(1,1)], simpleArray [(0,-4),(1,1)]] [])  
   -- x_1 + x_2 = 0, x_1 + x_2 = -3
  ,TestCase $ assertEqual "testArrayCheck 1004" (Nothing) (solveConstraints [simpleArray [(0,0),(1,1),(2,1)], simpleArray [(0,3),(1,1),(2,1)]] [])  
   -- 4x_1 = 7
  ,TestCase $ assertEqual "testArrayCheck 1005" (Nothing) (solveConstraints [simpleArray [(0,-7),(1,4)]] [])
  ]
  where
    pass :: (Int, [[Integer]], [[Integer]], [[Integer]]) -> Test
    pass (ind, expIneq, inpEq, inpIneq) = TestCase $ assertEqual ("testArrayCheck " ++ show ind)
      (Just $ map arrayise expIneq) (solveConstraints (map arrayise inpEq) (map arrayise inpIneq))
    
arrayise :: [Integer] -> Array Int Integer
arrayise = simpleArray . zip [0..]

-- QuickCheck tests for Omega Test:
-- The idea is to begin with a random list of integers, representing transformed y_i variables.
-- This will be the solution.  Feed this into a random list of inequalities.  The inequalities do
-- not have to be true; they merely have to exist.  Then slowly transform 


--TODO generate negative coeffs, and allow zero coefficients (but be careful we don't
-- produce unsolveable equations, e.g. where one is all zeroes, or a_3 is zero in all of them)

-- | Generates a list of random numbers of the given size, where the numbers are all co-prime.
-- This is so they can be used as normalised coefficients in a linear equation
coprimeList :: Int -> Gen [Integer]
coprimeList size = do non_normal <- replicateM size $ choose (1,100)
                      return $ map (\x -> x `div` (foldl mygcd 0 non_normal)) non_normal

-- | Generates a list of lists of co-prime numbers, where each list is distinct.
-- The returned list of lists will be square; N equations, each with N items
distinctCoprimeLists :: Int -> Gen [[Integer]]
distinctCoprimeLists size = distinctCoprimeLists' [] size
  where
    -- n is the number left to generate; size is still the "width" of the lists
    distinctCoprimeLists' :: [[Integer]] -> Int -> Gen [[Integer]]
    distinctCoprimeLists' result 0 = return result
    distinctCoprimeLists' soFar n = do next <- coprimeList size
                                       if (next `elem` soFar)
                                         then distinctCoprimeLists' soFar n -- Try again
                                         else distinctCoprimeLists' (soFar ++ [next]) (n - 1)

-- | Given a solution, and the coefficients, work out the result.
-- Effectively the dot-product of the two lists.
calcUnits :: [Integer] -> [Integer] -> Integer
calcUnits a b = foldl (+) 0 $ zipWith (*) a b

-- | Given the solution for an equation (values of x_1 .. x_n), generates 
-- equalities and inequalities.  The equalities will all be true and consistent,
-- the inequalities will all turn out to be equal.  That is, when the inequalities
-- are resolved, the LHS will equal 0.  Therefore we can generate the inequalities
-- using the same method as equalities.  Also, the equalities are assured to be 
-- distinct.  If they were not distinct (one could be transformed into another by scaling)
-- then the equation set would be unsolveable.
generateEqualities :: [Integer] -> Gen (EqualityProblem, InequalityProblem)
generateEqualities solution = do eqCoeffs <- distinctCoprimeLists num_vars
                                 ineqCoeffs <- distinctCoprimeLists num_vars
                                 return (map mkCoeffArray eqCoeffs, map mkCoeffArray ineqCoeffs)
  where
    num_vars = length solution
    mkCoeffArray coeffs = arrayise $ (negate $ calcUnits solution coeffs) : coeffs

newtype OmegaTestInput = OMI (EqualityProblem, InequalityProblem) deriving (Show)

-- | Generates an Omega test problem with between 1 and 10 variables (incl), where the solutions
-- are numbers between -20 and + 20 (incl).
generateProblem :: Gen (EqualityProblem, InequalityProblem)
generateProblem = choose (1,10) >>= (\n -> replicateM n $ choose (-20,20)) >>= generateEqualities

instance Arbitrary OmegaTestInput where
  arbitrary = generateProblem >>* OMI

qcOmegaEquality :: [QuickCheckTest]
qcOmegaEquality = [scaleQC (40,200,2000,10000) prop]
  where
    prop (OMI (eq,ineq)) = omegaCheck actAnswer
      where
        actAnswer = solveConstraints eq ineq
        omegaCheck (Just ineqs) = all (all (== 0) . elems) ineqs
        omegaCheck Nothing = False

type MutatedEquation =
  (InequalityProblem
  ,Maybe ([(EqualityConstraintEquation,EqualityConstraintEquation)],InequalityProblem))

-- The type for inside the function; easier to work with since it can't be
-- inconsistent until the end.
type MutatedEquation' =
  (InequalityProblem
  ,[(EqualityConstraintEquation,EqualityConstraintEquation)]
  ,InequalityProblem)

-- | Given a distinct equation list, mutates each one at random using one of these mutations:
-- * Unchanged
-- * Generates similar but redundant equations
-- * Generates its dual (to be transformed into an equality equation)
-- * Generates an inconsistent partner (rare - 20% chance of existing in the returned problem).
-- The equations passed in do not have to be consistent, merely unique and normalised.
-- Returns the input, and the expected output.
mutateEquations :: InequalityProblem -> Gen MutatedEquation
mutateEquations ineq = do (a,b,c) <- mapM mutate ineq >>*
                                       foldl (\(a,b,c) (x,y,z) -> (a++x,b++y,c++z)) ([],[],[])
                          frequency
                            [
                              (80,return (a,Just (b,c)))
                             ,(20,addInconsistent a >>* (\x -> (x,Nothing)))
                            ]
  where
    -- We take an equation like 5 + 3x - y >=0 (i.e. 3x - y >= -5)
    -- and add -6 -3x + y >= 0 (i.e. -6 >= 3x - y)
    -- This works for all cases, even where the unit coeff is zero;
    -- 3x - y >= 0 becomes -1 -3x + y >= 0 (i.e. -1 >= 3x - y)
    addInconsistent :: InequalityProblem -> Gen InequalityProblem
    addInconsistent inpIneq
      = do randEq <- oneof (map return inpIneq)
           let negEq = amap negate randEq
           let modRandEq = (negEq) // [(0, (negEq ! 0) - 1)]
           return (modRandEq : inpIneq)

    mutate :: InequalityConstraintEquation -> Gen MutatedEquation'
    mutate ineq = oneof
                    [
                      return ([ineq],[],[ineq])
                     ,addRedundant ineq
                     ,return $ addDual ineq
                    ]

    addDual :: InequalityConstraintEquation -> MutatedEquation'
    addDual eq = ([eq,neg],[(eq,neg)],[]) where neg = amap negate eq

    addRedundant :: InequalityConstraintEquation -> Gen MutatedEquation'
    addRedundant ineq = do i <- choose (1,5) -- number of redundant equations to add
                           newIneqs <- replicateM i addRedundant'
                           return (ineq : newIneqs, [], [ineq])
                             where
                               -- A redundant equation is one with a bigger unit coefficient:
                               addRedundant' = do n <- choose (1,100)
                                                  return $ ineq // [(0,n + (ineq ! 0))]

newtype OmegaPruneInput = OPI MutatedEquation deriving (Show)

instance Arbitrary OmegaPruneInput where
  arbitrary = (generateProblem  >>= (return . snd) >>= mutateEquations) >>* OPI

qcOmegaPrune :: [QuickCheckTest]
qcOmegaPrune = [scaleQC (100,1000,10000,50000) prop]
  where
    --We perform the map assocs because we can't compare arrays using *==*
    -- (toConstr fails in the pretty-printing!).
    prop (OPI (inp,out)) =
      case out of
        Nothing -> Nothing *==* result
        Just (outEq,outIneq) ->
          case result of
            Nothing -> mkFailResult $ "Expected success but got failure: " ++ pshow (inp,out)
            Just (actEq,actIneq) ->
              (sort (map assocs actIneq) *==* sort (map assocs outIneq)) *&&* (checkEq actEq outEq)
      where
        result = pruneAndCheck inp

    checkEq :: [EqualityConstraintEquation] ->
      [(EqualityConstraintEquation,EqualityConstraintEquation)] -> Result
    checkEq [] [] = mkPassResult
    checkEq eqs [] = mkFailResult $ "checkEq: " ++ show eqs
    checkEq eqs ((x,y):xys)
      = case findAndRemove (\z -> z == x || z == y) eqs of
          (Just _, eqs') -> checkEq eqs' xys
          _ -> mkFailResult $ "checkEq: " ++ show eqs ++ " could not match: " ++ show (x,y)

qcTests :: (Test, [QuickCheckTest])
qcTests = (TestList
 [
  testGetVarProc
  ,testInitVar
--  ,testParUsageCheck
  ,testReachDef
  ,testArrayCheck
 ]
 ,qcOmegaEquality ++ qcOmegaPrune)



