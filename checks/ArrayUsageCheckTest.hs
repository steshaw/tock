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

module ArrayUsageCheckTest (vioqcTests) where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer (tell)
import Data.Array.IArray
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import qualified Data.Set as Set
import Prelude hiding ((**),fail)
import Test.HUnit
import Test.QuickCheck hiding (check)


import ArrayUsageCheck
import qualified AST as A
import CompState
import Metadata
import Omega
import ShowCode
import TestFramework
import TestHarness
import TestUtils
import Types
import UsageCheckUtils hiding (Var)
import qualified UsageCheckUtils
import Utils

instance Show FlattenedExp where
  show fexp = runIdentity $ showFlattenedExp (return . showOccam) fexp

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
  ,TestCase $ assertEqual "testArrayCheck 1002" (Nothing) (solveConstraints' [simpleArray [(0,7),(1,0)]] [])
   -- x_1 = 3, x_1 = 4
  ,TestCase $ assertEqual "testArrayCheck 1003" (Nothing) (solveConstraints' [simpleArray [(0,-3),(1,1)], simpleArray [(0,-4),(1,1)]] [])  
   -- x_1 + x_2 = 0, x_1 + x_2 = -3
  ,TestCase $ assertEqual "testArrayCheck 1004" (Nothing) (solveConstraints' [simpleArray [(0,0),(1,1),(2,1)], simpleArray [(0,3),(1,1),(2,1)]] [])  
   -- 4x_1 = 7
  ,TestCase $ assertEqual "testArrayCheck 1005" (Nothing) (solveConstraints' [simpleArray [(0,-7),(1,4)]] [])
  ]
  where
    solveConstraints' = solveConstraints undefined
  
    pass :: (Int, [[Integer]], [[Integer]], [[Integer]]) -> Test
    pass (ind, expIneq, inpEq, inpIneq) = TestCase $ assertEqual ("testArrayCheck " ++ show ind)
      (Just $ map arrayise expIneq) (transformMaybe snd $ solveConstraints' (map arrayise inpEq) (map arrayise inpIneq))
    
arrayise :: [Integer] -> Array Int Integer
arrayise = simpleArray . zip [0..]

-- Various helpers for easily creating equations.
-- Rules for writing equations:
-- * You must use the variables i, j, k in that order as you need them.
--   Never write an equation just involving i and k, or j and k.  Always
--   use (i), (i and j), or (i and j and k).
-- * Constant scaling must always be on the left, and does not need the con
--   function.  con 1 ** i won't compile.

-- Useful to make sure the equation types are not mixed up:
newtype HandyEq = Eq [(Int, Integer)] deriving (Show, Eq)
newtype HandyIneq = Ineq [(Int, Integer)] deriving (Show, Eq)

-- | The constraint for an arbitrary i,j that exist between low and high (inclusive)
-- and where i and j are distinct and i is taken to be the lower index.
i_j_constraint :: Integer -> Integer -> [HandyIneq]
i_j_constraint low high = [con low <== i, i ++ con 1 <== j, j <== con high]

-- The easy way of writing equations is built on the following Haskell magic.
-- Essentially, everything is a list of (index, coefficient).  You can scale
-- with the ** operator, and you can form equalities and inequalities with
-- the ===, <== and >== operators.  The type system saves you from doing anything
-- nonsensical.  The other neat thing is that + is ++.  An &&& operator is defined
-- for combining inequality lists.

leq :: [[(Int,Integer)]] -> [HandyIneq]
leq [] = []
leq [_] = []
leq (x:y:zs) = (x <== y) : (leq (y:zs))

(&&&) :: [a] -> [a] -> [a]
(&&&) = (++)
  
infixr 4 ===
infixr 4 <==
infixr 4 >==
infix  6 **
  
(===) :: [(Int,Integer)] -> [(Int,Integer)] -> HandyEq
lhs === rhs = Eq $ lhs ++ negateVars rhs
(<==) :: [(Int,Integer)] -> [(Int,Integer)] -> HandyIneq
lhs <== rhs = Ineq $ negateVars lhs ++ rhs
(>==) :: [(Int,Integer)] -> [(Int,Integer)] -> HandyIneq
lhs >== rhs = Ineq $ lhs ++ negateVars rhs
negateVars :: [(Int,Integer)] -> [(Int,Integer)]
negateVars = map (transformPair id negate)
(**) :: Integer -> [(Int,Integer)] -> [(Int,Integer)]
n ** var = map (transformPair id (* n)) var
con :: Integer -> [(Int,Integer)]
con c = [(0,c)]
i,j,k,m,n,p :: [(Int, Integer)]
i = [(1,1)]
j = [(2,1)]
k = [(3,1)]
m = [(4,1)]
n = [(5,1)]
p = [(6,1)]

-- Turns a list like [(i,3),(j,4)] into proper answers
answers :: [([(Int, Integer)],Integer)] -> Map.Map CoeffIndex Integer
answers = Map.fromList . map (transformPair (fst . head) id)

-- Shows the answers in terms of the test variables
showTestAnswers :: VariableMapping -> String
showTestAnswers vm = concat $ intersperse "\n" $ map showAnswer $ Map.assocs vm 
  where
    showAnswer :: (CoeffIndex,EqualityConstraintEquation) -> String
    showAnswer (x,eq) = mylookup x ++ " = " ++ showItems eq 
    
showItems :: EqualityConstraintEquation -> String
showItems eq = concat (intersperse " + " (filter (not . null) $ map showItem (assocs eq)))

showItem :: (CoeffIndex,Integer) -> String
showItem (k,a_k) | a_k == 0  = ""
                 | k == 0    = show a_k
                 | a_k == 1  = mylookup k
                 | otherwise = show a_k ++ mylookup k
    
mylookup :: CoeffIndex -> String
mylookup x = Map.findWithDefault "unknown" x lookupTable
    
lookupTable :: Map.Map CoeffIndex String
lookupTable = Map.fromList $ zip [1..] ["i","j","k","m","n","p"]
                ++ [ (n,"y_" ++ show n) | n <- [7..100]] -- needed for showing QuickCheck failures

showInequality :: InequalityConstraintEquation -> String
showInequality ineq = "0 <= " ++ zeroIfBlank (showItems ineq)

showInequalities :: InequalityProblem -> String
showInequalities ineqs = concat $ intersperse "\n" $ map showInequality ineqs

showEquality :: InequalityConstraintEquation -> String
showEquality eq = "0 = " ++ zeroIfBlank (showItems eq)

showEqualities :: InequalityProblem -> String
showEqualities eqs = concat $ intersperse "\n" $ map showEquality eqs

zeroIfBlank :: String -> String
zeroIfBlank s | null s    = "0"
              | otherwise = s

showProblem :: (EqualityProblem,InequalityProblem) -> String
showProblem (eqs,ineqs) = showEqualities eqs ++ "\n" ++ showInequalities ineqs

makeConsistent :: [HandyEq] -> [HandyIneq] -> (EqualityProblem, InequalityProblem)
makeConsistent eqs ineqs = (map ensure eqs', map ensure ineqs')
  where
    eqs' = map (\(Eq e) -> e) eqs
    ineqs' = map (\(Ineq e) -> e) ineqs
    
    ensure :: [(CoeffIndex, Integer)] -> EqualityConstraintEquation
    ensure = accumArray (+) 0 (0, largestIndex)
    largestIndex = maximum $ map (maximum . map fst) $ [[(0,0)]] ++ eqs' ++ ineqs'


-- | Returns Nothing if there is definitely no solution, or (Just ineq) if 
-- further investigation is needed


solveAndPrune' :: VariableMapping -> EqualityProblem -> InequalityProblem -> Maybe (VariableMapping,InequalityProblem)
solveAndPrune' vm [] ineq = return (vm,ineq)
solveAndPrune' vm eq ineq = solveConstraints vm eq ineq >>= (seqPair . transformPair return pruneIneq) >>= (\(x,(y,z)) -> solveAndPrune' x y z)

solveAndPrune :: EqualityProblem -> InequalityProblem -> Maybe (VariableMapping,InequalityProblem)
solveAndPrune eq ineq = solveAndPrune' (defaultMapping maxVar) eq ineq
  where
    maxVar = if null eq && null ineq then 0 else
                if null eq then snd $ bounds $ head ineq else snd $ bounds $ head eq


-- | A problem's "solveability"; essentially how much of the Omega Test do you have to
-- run before the result is known, and which result is it
data Solveability = 
  SolveEq (Map.Map CoeffIndex Integer)
              -- ^ Solveable just by solving equalities and pruning.
              -- In other words, solveAndPrune will give (Just [])
  | ImpossibleEq -- ^ Definitely not solveable just from the equalities.
                 -- In other words, solveAndPrune will give Nothing
  | SolveIneq -- ^ Reduceable to inequalities, where the inequalities (therefore) have a solution.
              -- In other words, solveAndPrune will give (Just a) (a /= []),
              -- and then feeding a through fmElimination will give back an inequality set
              -- that can be fed into <SOME FUNCTION TODO> to give a possible solution
  | ImpossibleIneq -- ^ The inequalities are impossible to solve.
                   -- In other words, solveAndPrune will give (Just a) (a /= []),
                   -- but feeding this through fmElimination will give Nothing.
  -- TODO do we need an option where one variable is left in the inequalities?
  deriving (Eq,Show)

check :: Solveability -> (Int,[HandyEq], [HandyIneq]) -> Test
check s (ind, eq, ineq) =
  case s of
    ImpossibleEq   -> TestCase $ assertEqual testName Nothing sapped
    SolveEq ans    -> TestCase $ assertEqual testName (Just (ans,[]))
                                   (transformMaybe (transformPair getCounterEqs id) sapped)
    ImpossibleIneq -> TestCase $ assertEqual testName Nothing elimed
    SolveIneq      -> TestCase $ assertBool  testName (isJust elimed) -- TODO check for a solution to the inequality
    where problem = makeConsistent eq ineq
          sapped = uncurry solveAndPrune problem
          elimed = uncurry solveProblem problem
          testName = "check " ++ show s ++ " " ++ show ind
            ++ "(VM after pruning was: " ++ showMaybe showTestAnswers (transformMaybe fst sapped) ++ 
            ", ineqs: " ++ showMaybe showInequalities (transformMaybe snd sapped) ++ ")"

testMakeEquations :: Test
testMakeEquations = TestLabel "testMakeEquations" $ TestList
  [
    test (0,[(Map.empty,[con 0 === con 1],leq [con 0,con 1,con 7] &&& leq [con 0,con 2,con 7])],
      [intLiteral 1, intLiteral 2],intLiteral 8)
     
   ,test (1,[(i_mapping,[i === con 3],leq [con 0,con 3,con 7] &&& leq [con 0,i,con 7])],
      [exprVariable "i",intLiteral 3],intLiteral 8)
   
   ,test (2,[(ij_mapping,[i === j],leq [con 0,i,con 7] &&& leq [con 0,j,con 7])],
      [exprVariable "i",exprVariable "j"],intLiteral 8)

   ,test (3,[(ij_mapping,[i ++ con 3 === j],leq [con 0,i ++ con 3,con 7] &&& leq [con 0,j,con 7])],
      [buildExpr $ Dy (Var "i") A.Add (Lit $ intLiteral 3),exprVariable "j"],intLiteral 8)
     
   ,test (4,[(ij_mapping,[2 ** i === j],leq [con 0,2 ** i,con 7] &&& leq [con 0,j,con 7])],
      [buildExpr $ Dy (Var "i") A.Mul (Lit $ intLiteral 2),exprVariable "j"],intLiteral 8)

   ,test' (5, [(((0,[]),(1,[])), ijk_mapping, [j === k], leq [con 0, j, i ++ con (-1)] &&& leq [con 0, k, i ++ con (-1)])],
     [exprVariable "j", exprVariable "k"], exprVariable "i")

   -- Testing (i REM 3) vs (4)
   ,test' (10,[
        (( (0,[XZero]), (1,[]) ) ,i_mod_mapping 3,
          [con 0 === con 4, i === con 0], leq [con 0,con 0,con 7] &&& leq [con 0,con 4,con 7])
       ,(( (0,[XPos]), (1,[]) ), i_mod_mapping 3,
         [i ++ 3 ** j === con 4], leq [con 0,con 4,con 7] &&& leq [con 0,i ++ 3 ** j,con 7] &&& [i >== con 1] &&& [j <== con 0] &&& leq [con 0, i ++ 3 ** j, con 2])
       ,(( (0,[XNeg]), (1,[]) ), i_mod_mapping 3,
         [i ++ 3 ** j === con 4], leq [con 0,con 4,con 7] &&& leq [con 0,i ++ 3 ** j,con 7] &&& [i <== con (-1)] &&& [j >== con 0] &&& leq [con (-2), i ++ 3 ** j, con 0])
      ],[buildExpr $ Dy (Var "i") A.Rem (Lit $ intLiteral 3),intLiteral 4],intLiteral 8)
      
   -- Testing ((3*i - 2*j REM 11) - 5) vs (i + j)
   -- Expressed as ((2 * (i - j)) + i) REM 11 - 5, and i + j
   ,test' (11,[
        (( (0,[XZero]), (1,[]) ), _3i_2j_mod_mapping 11,
          [con (-5) === i ++ j, 3**i ++ (-2)**j === con 0], leq [con 0,con (-5),con 7] &&& leq [con 0,i ++ j,con 7])
       ,(( (0,[XPos]), (1,[]) ), _3i_2j_mod_mapping 11,
          [3**i ++ (-2)**j ++ 11 ** k ++ con (-5) === i ++ j],
          leq [con 0,i ++ j,con 7] &&& leq [con 0,3**i ++ (-2)**j ++ 11 ** k ++ con (-5),con 7]
          &&& [3**i ++ (-2)**j >== con 1] &&& [k <== con 0] &&& leq [con 0, 3**i ++ (-2)**j ++ 11 ** k, con 10])
       ,(( (0,[XNeg]), (1,[]) ), _3i_2j_mod_mapping 11,
          [3**i ++ (-2)**j ++ 11 ** k ++ con (-5) === i ++ j],
          leq [con 0,i ++ j,con 7] &&& leq [con 0,3**i ++ (-2)**j ++ 11 ** k ++ con (-5),con 7]
          &&& [3**i ++ (-2)**j <== con (-1)] &&& [k >== con 0] &&& leq [con (-10), 3**i ++ (-2)**j ++ 11 ** k, con 0])
      ],[buildExpr $
           Dy (Dy (Dy (Dy (Lit $ intLiteral 2)
                       A.Mul (Dy (Var "i") A.Subtr (Var "j"))
                      )
                   A.Add (Var "i")
                  )
               A.Rem (Lit $ intLiteral 11)
              )
           A.Subtr (Lit $ intLiteral 5)
        ,buildExpr $ Dy (Var "i") A.Add (Var "j")],intLiteral 8)
   
   -- Testing i REM 2 vs (i + 1) REM 4
   ,test' (12,combine (0,1) (i_ip1_mod_mapping 2 4)
     [ ([XZero],[XZero],[([con 0 === con 0],[]),rr_i_zero, rr_ip1_zero])
      ,([XZero],[XPos],[([con 0 === i ++ con 1 ++ 4**k],[]),rr_i_zero,rr_ip1_pos])
      ,([XZero],[XNeg],[([con 0 === i ++ con 1 ++ 4**k],[]),rr_i_zero,rr_ip1_neg])
      ,([XPos],[XZero],[([i ++ 2**j === con 0],[]),rr_i_pos,rr_ip1_zero])
      ,([XPos],[XPos],[([i ++ 2**j === i ++ con 1 ++ 4**k],[]),rr_i_pos,rr_ip1_pos])
      ,([XPos],[XNeg],[([i ++ 2**j === i ++ con 1 ++ 4**k],[]),rr_i_pos,rr_ip1_neg])
      ,([XNeg],[XZero],[([i ++ 2**j === con 0],[]),rr_i_neg,rr_ip1_zero])
      ,([XNeg],[XPos],[([i ++ 2**j === i ++ con 1 ++ 4**k],[]),rr_i_neg,rr_ip1_pos])
      ,([XNeg],[XNeg],[([i ++ 2**j === i ++ con 1 ++ 4**k],[]),rr_i_neg,rr_ip1_neg])
     ], [buildExpr $ Dy (Var "i") A.Rem (Lit $ intLiteral 2)
        ,buildExpr $ Dy (Dy (Var "i") A.Add (Lit $ intLiteral 1)) A.Rem (Lit $ intLiteral 4)
        ], intLiteral 8)
      
   -- Testing i REM j vs 3
   ,test' (100,[
     -- i = 0:
     (((0,[XZero]),(1,[])),i_mod_j_mapping,
       [con 0 === con 3, i === con 0], leq [con 0, con 0, con 7] &&& leq [con 0, con 3, con 7])
     -- i positive, j positive, i REM j = i:
    ,(((0,[XPosYPosAZero]),(1,[])),i_mod_j_mapping,
      [i === con 3], [i >== con 1] &&& leq [con 0, i, j ++ con (-1)] &&& leq [con 0, i, con 7] &&& leq [con 0, con 3, con 7])
     -- i positive, j positive, i REM j = i + k:
    ,(((0,[XPosYPosANonZero]),(1,[])),i_mod_j_mapping,
      [i ++ k === con 3], [i >== con 1, k <== (-1)**j] &&& 
        leq [con 0, i ++ k, j ++ con (-1)] &&& leq [con 0, i ++ k, con 7] &&& leq [con 0, con 3, con 7])
     -- i positive, j negative, i REM j = i:
    ,(((0,[XPosYNegAZero]),(1,[])),i_mod_j_mapping,
      [i === con 3], [i >== con 1] &&& leq [con 0, i, (-1)**j ++ con (-1)] &&& leq [con 0, i, con 7] &&& leq [con 0, con 3, con 7])
     -- i positive, j negative, i REM j = i + k:
    ,(((0,[XPosYNegANonZero]),(1,[])),i_mod_j_mapping,
      [i ++ k === con 3], [i >== con 1, k <== j] &&& 
        leq [con 0, i ++ k, (-1)**j ++ con (-1)] &&& leq [con 0, i ++ k, con 7] &&& leq [con 0, con 3, con 7])

     -- i negative, j positive, i REM j = i:
    ,(((0,[XNegYPosAZero]),(1,[])),i_mod_j_mapping,
      [i === con 3], [i <== con (-1)] &&& leq [(-1)**j ++ con 1, i, con 0] &&& leq [con 0, i, con 7] &&& leq [con 0, con 3, con 7])
     -- i negative, j positive, i REM j = i + k:
    ,(((0,[XNegYPosANonZero]),(1,[])),i_mod_j_mapping,
      [i ++ k === con 3], [i <== con (-1), k >== j] &&& 
        leq [(-1)**j ++ con 1, i ++ k, con 0] &&& leq [con 0, i ++ k, con 7] &&& leq [con 0, con 3, con 7])
     -- i negative, j negative, i REM j = i:
    ,(((0,[XNegYNegAZero]),(1,[])),i_mod_j_mapping,
      [i === con 3], [i <== con (-1)] &&& leq [j ++ con 1, i, con 0] &&& leq [con 0, i, con 7] &&& leq [con 0, con 3, con 7])
     -- i negative, j negative, i REM j = i + k:
    ,(((0,[XNegYNegANonZero]),(1,[])),i_mod_j_mapping,
      [i ++ k === con 3], [i <== con (-1), k >== (-1)**j] &&& 
        leq [j ++ con 1, i ++ k, con 0] &&& leq [con 0, i ++ k, con 7] &&& leq [con 0, con 3, con 7])
   ], [buildExpr $ Dy (Var "i") A.Rem (Var "j"), intLiteral 3], intLiteral 8)


   -- i vs. i'
   ,testRep' (199,[(((0,[]),(0,[])),rep_i_mapping, [i === j],
       leq [con 3, i, con 4] &&& leq [con 3, j, con 4]  &&& [i <== j ++ con (-1)]
       &&& leq [con 0, i, con 7] &&& leq [con 0, j, con 7])],
     ("i", intLiteral 3, intLiteral 2),[exprVariable "i"],intLiteral 8)

   -- i vs. i'
   ,testRep' (200,[(((0,[]),(0,[])),rep_i_mapping, [i === j],
       ij_16 &&& [i <== j ++ con (-1)]
       &&& leq [con 0, i, con 7] &&& leq [con 0, j, con 7])],
     ("i", intLiteral 1, intLiteral 6),[exprVariable "i"],intLiteral 8)
     
   -- i vs i' vs 3
   ,let common = ij_16 &&& [i <== j ++ con (-1)] in testRep' (201,
     [(((0,[]),(0,[])),rep_i_mapping, [i === j],
       common &&& leq [con 0, i, con 7] &&& leq [con 0, j, con 7])]
     ++ replicate 2 (((0,[]),(1,[])),rep_i_mapping,[i === con 3], common
          &&& leq [con 0, i, con 7] &&& leq [con 0, con 3, con 7])
     ++ [(((1,[]),(1,[])),rep_i_mapping,[con 3 === con 3],common &&& (concat $ replicate 2 (leq [con 0, con 3, con 7])))]
     ,("i", intLiteral 1, intLiteral 6),[exprVariable "i", intLiteral 3],intLiteral 8)

   -- i vs i + 1 vs i' vs i' + 1
   ,let common = ij_16 &&& [i <== j ++ con (-1)] in testRep' (202,[
        (((0,[]),(1,[])),rep_i_mapping,[i === j ++ con 1],common &&& leq [con 0, i, con 7] &&& leq [con 0, j ++ con 1, con 7])
       ,(((0,[]),(1,[])),rep_i_mapping,[i ++ con 1 === j],common &&& leq [con 0, i ++ con 1, con 7] &&& leq [con 0, j, con 7])
       ,(((0,[]),(0,[])),rep_i_mapping,[i === j],common &&& leq [con 0, i, con 7] &&& leq [con 0, j, con 7])
       ,(((1,[]),(1,[])),rep_i_mapping,[i === j],common &&& leq [con 0, i ++ con 1, con 7] &&& leq [con 0, j ++ con 1, con 7])]
       ++ [(((0,[]),(1,[])),rep_i_mapping, [i === i ++ con 1], common &&&
             leq [con 0, i, con 7] &&& leq [con 0,i ++ con 1, con 7])]
     ,("i", intLiteral 1, intLiteral 6),[exprVariable "i", buildExpr $ Dy (Var "i") A.Add (Lit $ intLiteral 1)],intLiteral 8)

   -- Only a constant:
   ,testRep' (210,[(((0,[]),(0,[])),rep_i_mapping,[con 4 === con 4],ij_16 &&& [i <== j ++ con (-1)] &&& (concat $ replicate 2 $ leq [con 0, con 4, con 7]))]
     ,("i", intLiteral 1, intLiteral 6),[intLiteral 4],intLiteral 8)


   -- i REM 3 vs i' REM 3
   ,testRep' (220,[
      -- i REM 3 == 0 and i' REM 3 == 0   
      (((0,[XZero]),(0,[XZero])), rep_i_mod_mapping 3, [con 0 === con 0, i === con 0, j === con 0], ij_16 &&& [i <== j ++ con (-1)] &&& leq [con 0, con 0, con 7] &&& leq [con 0, con 0, con 7])
      -- i REM 3 == 0 and i' >= 1
     ,(((0,[XZero]),(0,[XPos])), rep_i_mod_mapping 3, [con 0 === j ++ 3**m, i === con 0], ij_16 &&& [i <== j ++ con (-1)] &&& leq [con 0, con 0, con 7]
        &&& leq [con 0, j ++ 3**m, con 7] &&& [m <== con 0, j >== con 1] &&& leq [con 0, j ++ 3**m, con 2])
      -- i REM 3 == 0 and i' <= -1
     ,(((0,[XZero]),(0,[XNeg])), rep_i_mod_mapping 3, [con 0 === j ++ 3**m, i === con 0], ij_16 &&& [i <== j ++ con (-1)] &&& leq [con 0, con 0, con 7]
        &&& leq [con 0, j ++ 3**m, con 7] &&& [m >== con 0, j <== con (-1)] &&& leq [con (-2), j ++ 3**m, con 0])
      -- i >= 1 and i' REM 3 == 0
     ,(((0,[XPos]),(0,[XZero])), rep_i_mod_mapping 3, [i ++ 3**k === con 0, j === con 0], ij_16 &&& [i <== j ++ con (-1)] &&& leq [con 0, con 0, con 7]
        &&& leq [con 0, i ++ 3**k, con 7] &&& [k <== con 0, i >== con 1] &&& leq [con 0, i ++ 3**k, con 2])
      -- i >= 1 and i' >= 1
     ,(((0,[XPos]),(0,[XPos])), rep_i_mod_mapping 3, [i ++ 3**k === j ++ 3**m], ij_16 &&&  [i <== j ++ con (-1)]
       &&& leq [con 0, i ++ 3**k, con 7] &&& leq [con 0, j ++ 3**m, con 7]
       &&& [m <== con 0, k <== con 0, i >== con 1, j >== con 1]
       &&& leq [con 0, i ++ 3**k, con 2] &&& leq [con 0, j ++ 3**m, con 2])
      -- i >= 1 and i' <= -1
     ,(((0,[XPos]),(0,[XNeg])), rep_i_mod_mapping 3, [i ++ 3**k === j ++ 3**m], ij_16 &&&  [i <== j ++ con (-1)]
       &&& leq [con 0, i ++ 3**k, con 7] &&& leq [con 0, j ++ 3**m, con 7]
       &&& [m >== con 0, k <== con 0, i >== con 1, j <== con (-1)]
       &&& leq [con 0, i ++ 3**k, con 2] &&& leq [con (-2), j ++ 3**m, con 0])
      -- i <= -1 and i' REM 3 == 0
     ,(((0,[XNeg]),(0,[XZero])), rep_i_mod_mapping 3, [i ++ 3**k === con 0, j === con 0], ij_16 &&& [i <== j ++ con (-1)] &&& leq [con 0, con 0, con 7]
        &&& leq [con 0, i ++ 3**k, con 7] &&& [k >== con 0, i <== con (-1)] &&& leq [con (-2), i ++ 3**k, con 0])
      -- i <= - 1 and i' >= 1
     ,(((0,[XNeg]),(0,[XPos])), rep_i_mod_mapping 3, [i ++ 3**k === j ++ 3**m], ij_16 &&&  [i <== j ++ con (-1)]
       &&& leq [con 0, i ++ 3**k, con 7] &&& leq [con 0, j ++ 3**m, con 7]
       &&& [m <== con 0, k >== con 0, i <== con (-1), j >== con 1]
       &&& leq [con (-2), i ++ 3**k, con 0] &&& leq [con 0, j ++ 3**m, con 2])
      -- i <= - 1 and i' <= -1
     ,(((0,[XNeg]),(0,[XNeg])), rep_i_mod_mapping 3, [i ++ 3**k === j ++ 3**m], ij_16 &&&  [i <== j ++ con (-1)]
       &&& leq [con 0, i ++ 3**k, con 7] &&& leq [con 0, j ++ 3**m, con 7]
       &&& [m >== con 0, k >== con 0, i <== con (-1), j <== con (-1)]
       &&& leq [con (-2), i ++ 3**k, con 0] &&& leq [con (-2), j ++ 3**m, con 0])
     ],("i", intLiteral 1, intLiteral 6),[buildExpr $ Dy (Var "i") A.Rem (Lit $ intLiteral 3)], intLiteral 8)


   -- TODO test reads and writes are paired properly
   
   -- TODO test background knowledge being used
  ]
  where
    -- These functions assume that you pair each list [x,y,z] as (x,y) (x,z) (y,z) in that order.
    -- for more control use the test' and testRep' versions:
    test :: (Integer,[(VarMap,[HandyEq],[HandyIneq])],[A.Expression],A.Expression) -> Test
    test (ind, problems, exprs, upperBound) = test' (ind, zipWith (\n (vm,eq,ineq) -> (n,vm,eq,ineq)) (labelNums 0 $ length exprs) problems, exprs, upperBound)

    -- The ordering for the original list [0,1,2] should be [(0,1),(0,2),(1,2)]
    -- So take each number, pair it with each remaining number in order, then increase
    labelNums :: Int -> Int -> [((Int,[a]),(Int,[a]))]
    labelNums m n | m >= n    = []
                  | otherwise = [((m,[]),(n',[])) | n' <- [(m + 1) .. n]] ++ labelNums (m + 1) n 
    

    makeParItems :: BK -> [A.Expression] -> ParItems (BK, [A.Expression],[A.Expression])
    makeParItems bk es = ParItems $ map (\e -> SeqItems [(bk,[e],[])]) es
  
    lookup :: [A.Expression] -> (Int, a) -> (A.Expression, a)
    lookup es (n,b) = (es !! n, b)
  
    test' :: (Integer,[(((Int, [ModuloCase]),(Int,[ModuloCase])),VarMap,[HandyEq],[HandyIneq])],[A.Expression],A.Expression) -> Test
    test' (ind, problems, exprs, upperBound) = 
      TestCase $ assertEquivalentProblems ("testMakeEquations " ++ show ind)
        (map (\((a0,a1),b,c,d) -> ((lookup exprs a0, lookup exprs a1), b, makeConsistent c d)) problems)
          =<< (checkRight $ makeEquations (makeParItems [] exprs) upperBound)
  
    testRep' :: (Integer,[(((Int,[ModuloCase]), (Int,[ModuloCase])), VarMap,[HandyEq],[HandyIneq])],(String, A.Expression, A.Expression),[A.Expression],A.Expression) -> Test
    testRep' (ind, problems, (repName, repFrom, repFor), exprs, upperBound) = 
      TestCase $ assertEquivalentProblems ("testMakeEquations " ++ show ind)
        (map (\((a0,a1),b,c,d) -> ((lookup exprs a0, lookup exprs a1), b, makeConsistent c d)) problems)
          =<< (checkRight $ makeEquations (RepParItem (simpleName "i", A.For emptyMeta repFrom repFor (makeConstant emptyMeta 1)) $
            makeParItems [Map.fromList [(UsageCheckUtils.Var $ variable "i",
              [RepBoundsIncl (variable "i") repFrom (subOne $ addExprs repFrom repFor)])]] exprs) upperBound)
  
    pairLatterTwo (l,a,b,c) = (l,a,(b,c))

    joinMapping :: [VarMap] -> ([HandyEq],[HandyIneq]) -> [(VarMap,[HandyEq],[HandyIneq])]
    joinMapping vms (eq,ineq) = map (\vm -> (vm,eq,ineq)) vms
  
    i_mapping :: VarMap
    i_mapping = Map.singleton (Scale 1 $ (exprVariable "i",0)) 1
    ij_mapping :: VarMap
    ij_mapping = Map.fromList [(Scale 1 $ (exprVariable "i",0),1),(Scale 1 $ (exprVariable "j",0),2)]
    ijk_mapping :: VarMap
    ijk_mapping = Map.fromList [(Scale 1 $ (exprVariable "i",0),1),(Scale 1 $ (exprVariable "j",0),2),(Scale 1 $ (exprVariable "k",0),3)]
    i_mod_mapping :: Integer -> VarMap
    i_mod_mapping n = Map.fromList [(Scale 1 $ (exprVariable "i",0),1),(Modulo 1 (Set.singleton $ Scale 1 $ (exprVariable "i",0)) (Set.singleton $ Const n),2)]
    i_mod_j_mapping :: VarMap
    i_mod_j_mapping = Map.fromList [(Scale 1 $ (exprVariable "i",0),1),(Scale 1 $ (exprVariable "j",0),2),
      (Modulo 1 (Set.singleton $ Scale 1 $ (exprVariable "i",0)) (Set.singleton $ Scale 1 $ (exprVariable "j",0)),3)]
    _3i_2j_mod_mapping n = Map.fromList [(Scale 1 $ (exprVariable "i",0),1),(Scale 1 $ (exprVariable "j",0),2),
      (Modulo 1 (Set.fromList [(Scale 3 $ (exprVariable "i",0)),(Scale (-2) $ (exprVariable "j",0))]) (Set.singleton $ Const n),3)]
    -- i REM m, i + 1 REM n
    i_ip1_mod_mapping m n = Map.fromList [(Scale 1 $ (exprVariable "i",0),1)
      ,(Modulo 1 (Set.singleton $ Scale 1 $ (exprVariable "i",0)) (Set.singleton $ Const m),2)
      ,(Modulo 1 (Set.fromList [Scale 1 $ (exprVariable "i",0), Const 1]) (Set.singleton $ Const n),3)
     ]

    rep_i_mapping :: VarMap
    rep_i_mapping = Map.fromList [((Scale 1 (exprVariable "i",0)),1), ((Scale 1 (exprVariable "i",1)),2)]
    rep_i_mapping' :: VarMap
    rep_i_mapping' = Map.fromList [((Scale 1 (exprVariable "i",0)),2), ((Scale 1 (exprVariable "i",1)),1)]

    both_rep_i = joinMapping [rep_i_mapping, rep_i_mapping']
    
    rep_i_mod_mapping :: Integer -> VarMap
    rep_i_mod_mapping n = Map.fromList [((Scale 1 (exprVariable "i",0)),1), ((Scale 1 (exprVariable "i",1)),2)
      ,(Modulo 1 (Set.singleton $ Scale 1 $ (exprVariable "i",0)) (Set.singleton $ Const n),3)
      ,(Modulo 1 (Set.singleton $ Scale 1 $ (exprVariable "i",1)) (Set.singleton $ Const n),4)]

    -- Helper functions for i REM 2 vs (i + 1) REM 4.  Each one is a pair of equalities, inequalities
    rr_i_zero = ([i === con 0], leq [con 0,con 0,con 7])
    rr_ip1_zero = ([i ++ con 1 === con 0], leq [con 0,con 0,con 7])
    rr_i_pos = ([], leq [con 0, i ++ 2**j, con 7] &&& [i >== con 1, j <== con 0] &&& leq [con 0, i ++ 2**j, con 1])
    rr_ip1_pos = ([], leq [con 0, i ++ con 1 ++ 4**k, con 7] &&& [i ++ con 1 >== con 1, k <== con 0] &&& leq [con 0,  i ++ con 1 ++ 4**k, con 3])
    rr_i_neg = ([], leq [con 0, i ++ 2**j, con 7] &&& [i <== con (-1), j >== con 0] &&& leq [con (-1), i ++ 2**j, con 0])
    rr_ip1_neg = ([], leq [con 0, i ++ con 1 ++ 4**k, con 7] &&& [i ++ con 1 <== con (-1), k >== con 0] &&& leq [con (-3), i ++ con 1 ++ 4**k, con 0])

    combine :: (Int,Int) -> VarMap -> [([ModuloCase],[ModuloCase],[([HandyEq],[HandyIneq])])] -> [(((Int,[ModuloCase]),(Int,[ModuloCase])),VarMap,[HandyEq],[HandyIneq])]
    combine (l0,l1) vm eq_ineqs = [(((l0,m0),(l1,m1)),vm,e,i) | (m0,m1,(e,i)) <- map (\(a,b,c) -> (a,b,transformPair concat concat $ unzip c)) eq_ineqs]
    
    -- Helper functions for the replication:
    
    ij_16 = leq [con 1, i, con 6] &&& leq [con 1, j, con 6]

testMakeEquation :: TestMonad m r => ([(((A.Expression, [ModuloCase]), (A.Expression, [ModuloCase])), VarMap,[HandyEq],[HandyIneq])],ParItems [A.Expression],A.Expression) -> m ()
testMakeEquation (problems, exprs, upperBound) =
 assertEquivalentProblems ""
   (map (\(x,y,z) -> (x, y, uncurry makeConsistent z)) $ map pairLatterTwo problems) =<< (checkRight $ makeEquations (transformParItems pairWithEmpty exprs) upperBound)
  where
    pairWithEmpty a = ([],a,[])
    pairLatterTwo (l,a,b,c) = (l,a,(b,c))

-- TODO add background knowledge
-- TODO add replicators
newtype MakeEquationInput = MEI ([(((A.Expression, [ModuloCase]), (A.Expression, [ModuloCase])), VarMap,[HandyEq],[HandyIneq])],ParItems [A.Expression],A.Expression)

-- Show isn't very useful on QuickCheck failure in this case and just spams the screen:
instance Show MakeEquationInput where
  show = const ""

instance Arbitrary MakeEquationInput where
  arbitrary = generateEquationInput >>* MEI

frequency' :: [(Int, StateT s Gen a)] -> StateT s Gen a
frequency' items = do dist <- lift $ choose (0, (sum $ map fst items) - 1)
                      findDist dist items
  where
    findDist n ((sz, x):sxs)
      | n < sz     = x
      | otherwise = findDist (n - sz) sxs

-- | The item corresponding to the 
type GenEqItems = (A.Expression, [(CoeffIndex, Integer)])

-- exprDepth is only really used to stop the possible infinite recursion in the multiplied variable * expression.
-- All other recursions are barred by never recursing with specialAllowed = True (outside of the above item)

-- Generates a new variable, or multiplied variable pair
genNewItem :: Int -> Bool -> StateT VarMap Gen (GenEqItems, FlattenedExp)
genNewItem exprDepth specialAllowed
           = do (exp, fexp, nextId) <- frequency' $
                  [(80, do m <- get
                           let nextId = 1 + maximum (0 : Map.elems m)
                           let exp = exprVariable $ "x" ++ show nextId
                           return (exp, Scale 1 (exp,0), nextId))
                  ,(20, if exprDepth <= 1
                          then
                            do m <- get
                               let nextId = 1 + maximum (0 : Map.elems m)
                               let exp = A.Dyadic emptyMeta A.Mul (exprVariable $ "y" ++ show nextId) (exprVariable $ "y" ++ show nextId)
                               return (exp,Scale 1 (exp, 0), nextId)
                          else
                            do m <- get
                               ((expToMult,_),_) <- genNewItem (exprDepth - 1) True
                               -- We deliberately overwrite the state here, because we don't need/want the items
                               -- produced in expToMult to be in the variable map (the real code won't bother
                               -- inserting them, only the multiplied item
                               put m
                               let nextId = 1 + maximum (0 : Map.elems m)
                               let exp = A.Dyadic emptyMeta A.Mul (exprVariable $ "y" ++ show nextId) expToMult
                               return (exp, Scale 1 (exp, 0), nextId)
                   )
                  ] ++ if not specialAllowed then []
                         else [(10, do ((eT,iT),fT) <- genNewExp (exprDepth - 1) False True
                                       ((eB,iB),fB) <- genNewExp (exprDepth - 1) False True
                                       m <- get
                                       let nextId = 1 + maximum (0 : Map.elems m)
                                       return (A.Dyadic emptyMeta A.Rem eT eB, Modulo 1 (errorOrRight $ makeExpSet fT) (errorOrRight $ makeExpSet fB), nextId)
                              ),(10,do ((eT,iT),fT) <- genNewExp (exprDepth - 1) False True
                                       ((eB,iB),fB) <- genConst
                                       m <- get
                                       let nextId = 1 + maximum (0 : Map.elems m)
                                       return (A.Dyadic emptyMeta A.Div eT eB, Divide 1 (errorOrRight $ makeExpSet fT) (Set.singleton fB), nextId)
                              )]
                modify (Map.insert fexp nextId)
                return ((exp, [(nextId,1)]), fexp)

errorOrRight :: Show a => Either a b -> b
errorOrRight (Left x) = error $ "Not Right: Left " ++ show x
errorOrRight (Right x) = x

genConst :: StateT VarMap Gen (GenEqItems, FlattenedExp)
genConst = do val <- lift $ choose (1, 10)
              let exp = intLiteral val
              return ((exp, [(0,val)]), Const val)

genNewExp :: Int -> Bool -> Bool -> StateT VarMap Gen (GenEqItems, [FlattenedExp])
genNewExp exprDepth specialAllowed constAllowed
          = do num <- lift $ oneof $ map return [1,1,1,1,2,2,3] -- bias towards low numbers of items
               items <- replicateM num $ frequency' [(if constAllowed then 20 else 0, maybeMult genConst),
                                                     (80, maybeMult $ genNewItem (exprDepth - 1) specialAllowed)]
               return $ fromJust $ foldl join Nothing items
  where
    maybeMult :: StateT VarMap Gen (GenEqItems, FlattenedExp) -> StateT VarMap Gen (GenEqItems, FlattenedExp)
    maybeMult x = do multOrNot <- lift $ oneof $ map return [-1,0,0,0,0,1] -- bias towards not multiplying (represented by zero)
                     unmult <- x
                     case multOrNot of
                       0 -> return unmult
                       sign -> do mult' <- lift $ choose (1 :: Integer,10)
                                  let mult = sign * mult'
                                  return $ transformPair
                                    (transformPair (A.Dyadic emptyMeta A.Mul (intLiteral mult)) (map (transformPair id (* mult))))
                                    (scaleEq mult) unmult
    scaleEq :: Integer -> FlattenedExp -> FlattenedExp
    scaleEq k (Const n) = Const (k * n)
    scaleEq k (Scale n v) = Scale (k * n) v
    scaleEq k (Modulo n t b) = Modulo (k * n) t b
    scaleEq k (Divide n t b) = Divide (k * n) t b
  
    join :: Maybe (GenEqItems, [FlattenedExp]) -> (GenEqItems,FlattenedExp) -> Maybe (GenEqItems, [FlattenedExp])
    join Nothing (e,f) = Just (e,[f])
    join (Just ((ex,ix),fxs)) ((ey,iy),fy) = Just ((A.Dyadic emptyMeta A.Add ex ey, ix ++ iy),fxs ++ [fy])

generateEquationInput :: Gen ([(((A.Expression,[ModuloCase]), (A.Expression,[ModuloCase])),VarMap,[HandyEq],[HandyIneq])],ParItems [A.Expression],A.Expression)
generateEquationInput
 = do ((items, upper),vm) <- flip runStateT Map.empty
         (do upper <- frequency' [(80, genConst >>* fst), (20, genNewExp 4 False True >>* fst)]
             itemCount <- lift $ choose (1,5)
             items <- replicateM itemCount (genNewExp 2 True True)
             return (items, upper)
         )
      return (makeResults vm items upper, ParItems $ map (\((x,_),_) -> SeqItems [[x]]) items, fst upper)
  where
    makeResults :: VarMap ->
      [(GenEqItems, [FlattenedExp])] ->
      GenEqItems -> 
      [(((A.Expression,[ModuloCase]), (A.Expression,[ModuloCase])),VarMap,[HandyEq],[HandyIneq])]
    makeResults vm items upper = concatMap (flip (makeResult vm) upper) (allPairs items)
  
    makeResult :: VarMap -> ((GenEqItems, [FlattenedExp]), (GenEqItems, [FlattenedExp])) -> GenEqItems ->
      [(((A.Expression,[ModuloCase]), (A.Expression,[ModuloCase])),VarMap,[HandyEq],[HandyIneq])]
    makeResult vm (((ex,x),fx),((ey,y),fy)) (_,u) = mkItem (ex, moduloEq vm fx) (ey, moduloEq vm fy)
      where
        mkItem :: (A.Expression, [([ModuloCase], [(CoeffIndex, Integer)], [HandyEq], [HandyIneq])]) ->
                  (A.Expression, [([ModuloCase], [(CoeffIndex, Integer)], [HandyEq], [HandyIneq])]) ->
                  [(((A.Expression,[ModuloCase]), (A.Expression,[ModuloCase])),VarMap,[HandyEq],[HandyIneq])]
        mkItem (ex, xinfo) (ey, yinfo) = map (\(mx,my,eq,ineq) -> (((ex,mx),(ey,my)),vm,eq,ineq)) $ map (uncurry joinItems) (product2 (xinfo, yinfo))

        joinItems :: ([ModuloCase],[(CoeffIndex, Integer)], [HandyEq], [HandyIneq]) ->
                     ([ModuloCase],[(CoeffIndex, Integer)], [HandyEq], [HandyIneq]) ->
                     ([ModuloCase], [ModuloCase], [HandyEq],[HandyIneq])
        joinItems (mx, x, xEq, xIneq) (my, y, yEq, yIneq) = (mx, my, [x === y] &&& xEq &&& yEq, xIneq &&& yIneq &&& arrayBound x u &&& arrayBound y u)

    arrayBound :: [(CoeffIndex, Integer)] -> [(CoeffIndex, Integer)] -> [HandyIneq]
    arrayBound x u = leq [con 0, x, u ++ con (-1)]
    
    moduloEq :: VarMap -> [FlattenedExp] -> [([ModuloCase], [(CoeffIndex, Integer)], [HandyEq], [HandyIneq])]
    moduloEq vm es = foldl join [([],[],[],[])] (map (moduloEq' vm) es)
      where
        join :: [([ModuloCase], [(CoeffIndex, Integer)], [HandyEq], [HandyIneq])] ->
                [([ModuloCase], [(CoeffIndex, Integer)], [HandyEq], [HandyIneq])] ->
                [([ModuloCase], [(CoeffIndex, Integer)], [HandyEq], [HandyIneq])]
        join xs ys = map (uncurry join') $ product2 (xs,ys)
        
        join' :: ([ModuloCase], [(CoeffIndex, Integer)], [HandyEq], [HandyIneq]) ->
                 ([ModuloCase], [(CoeffIndex, Integer)], [HandyEq], [HandyIneq]) ->
                 ([ModuloCase], [(CoeffIndex, Integer)], [HandyEq], [HandyIneq])
        join' (msx, isx, eqsx, ineqsx) (msy, isy, eqsy, ineqsy) = (msx ++ msy, isx ++ isy, eqsx ++ eqsy, ineqsx ++ ineqsy)
        
    moduloEq' :: VarMap -> FlattenedExp -> [([ModuloCase], [(CoeffIndex, Integer)], [HandyEq], [HandyIneq])]
    moduloEq' vm m@(Modulo n top bottom) =
     let topVar = lookupFS (Set.toList top) vm
         botVar = lookupFS (Set.toList bottom) vm
         modVar = lookupF m vm
     in case onlyConst (Set.toList bottom) of
      Just c -> let v = topVar ++ (abs c)**modVar in
                [ ([XZero], [(0,0)], [topVar === con 0], [])
                , ([XPos], n**v, [], [topVar >== con 1, modVar <== con 0] &&& leq [con 0, v, con (abs c - 1)])
                , ([XNeg], n**v, [], [topVar <== con (-1), modVar >== con 0] &&& leq [con (1 - abs c), v, con 0])
                ]
      Nothing -> let v = topVar ++ modVar in
                 [ ([XZero], [(0,0)], [topVar === con 0], []) -- TODO stop the divisor being zero
                 
                 , ([XPosYPosAZero], n**topVar, [], [topVar >== con 1] &&& leq [con 0, topVar, botVar ++ con (-1)])
                 , ([XPosYNegAZero], n**topVar, [], [topVar >== con 1] &&& leq [con 0, topVar, (-1)**botVar ++ con (-1)])
                 , ([XNegYPosAZero], n**topVar, [], [topVar <== con (-1)] &&& leq [(-1)**botVar ++ con 1, topVar, con 0])
                 , ([XNegYNegAZero], n**topVar, [], [topVar <== con (-1)] &&& leq [botVar ++ con 1, topVar, con 0])
                 
                 , ([XPosYPosANonZero], n**v, [], [topVar >== con 1, modVar <== (-1)**botVar] &&& leq [con 0, v, botVar ++ con (-1)])
                 , ([XPosYNegANonZero], n**v, [], [topVar >== con 1, modVar <== botVar] &&& leq [con 0, v, (-1)**botVar ++ con (-1)])

                 , ([XNegYPosANonZero], n**v, [], [topVar <== con (-1), modVar >== botVar] &&& leq [(-1)**botVar ++ con 1, v, con 0])
                 , ([XNegYNegANonZero], n**v, [], [topVar <== con (-1), modVar >== (-1)**botVar] &&& leq [botVar ++ con 1, v, con 0])
                 ]
    moduloEq' vm m@(Divide n top bottom) =
            [ ([XZero], [(0,0)], [topVar === con 0], [])
            , ([XPos], n**divVar, [], [topVar >== con 1]  &&& eqs (resultSignum True))
            , ([XNeg], n**divVar, [], [topVar <== con (-1)] &&& eqs (resultSignum False))
            ]
            where
              topVar = lookupFS (Set.toList top) vm
              divVar = lookupF m vm
              c = fromJust $ onlyConst (Set.toList bottom)
              v = topVar ++ (-c)**divVar

              resultSignum xpos = signum c * (if xpos then 1 else -1)

              -- TopSign BottomSign Bounds:
              --  +++      +++       (0, c - 1)
              --  +++      ---       (c + 1, 0)   (or: 1 - abs c, 0)
              --  ---      +++       (1 - c, 0)
              --  ---      ---       (0, -1 - c)  (or: (0, abs c - 1)
              eqs sign = [sign**divVar >== con 0] &&& leq
                           (if signum c == sign
                             then [con 0, v, con (abs c - 1)]
                             else [con (1 - abs c), v, con 0])
    moduloEq' vm exp = [([], lookupF exp vm, [], [])]
    
    lookupFS :: [FlattenedExp] -> VarMap -> [(CoeffIndex, Integer)]
    lookupFS es vm = concatMap (flip lookupF vm) es
    
    lookupF :: FlattenedExp -> VarMap -> [(CoeffIndex, Integer)]
    lookupF (Const c) _ = con c
    lookupF f@(Scale a v) vm = [(fromJust $ Map.lookup f vm, a)]
     -- We don't scale modulo directly here because the modulo variable is a or m,
     -- which shouldn't be scaled
    lookupF f@(Modulo a t b) vm = [(fromJust $ Map.lookup f vm, 1)]
    lookupF f@(Divide a t b) vm = [(fromJust $ Map.lookup f vm, 1)]

--TODO deal with this counter-example (related to canonical form of expressions, I think):
--Keys in variable mapping [((9 * x9) + (-9 * x10)),(x7 + x8),(-10 * x6),(((8 * x3) + (y4 * y4)) / 2)]
--expected: [(y1 * ((x1 + (y2 * y2)) REM x3)),(y4 * y4),x10,x2,x3,x6,x7,x8,x9,((y4 * y4) + 8*x3 / 2)]
-- but got: [(y1 * (((y2 * y2) + x1) REM x3)),(y4 * y4),x10,x2,x3,x6,x7,x8,x9,((y4 * y4) + 8*x3 / 2)]

qcTestMakeEquations :: [LabelledQuickCheckTest]
qcTestMakeEquations = [("Turning Code Into Equations", scaleQC (20,100,400,1000) (runQCTest . prop))]
  where
    prop :: MakeEquationInput -> QCProp
    prop (MEI mei) = testMakeEquation mei

testIndexes :: Test
testIndexes = TestList
  [
  
    check (SolveEq $ answers [(i,7)]) (0, [i === con 7], [])
   ,check (SolveEq $ answers [(i,6)]) (1, [2 ** i === con 12], [])   
   ,check ImpossibleEq (2, [i === con 7],[i <== con 5])
    
   -- Can i = j?
   ,check ImpossibleEq (3, [i === j], i_j_constraint 0 9)

   -- Can (j + 1 % 10 == i + 1 % 10)?
   ,check ImpossibleIneq $ withKIsMod (i ++ con 1) 10 $ withNIsMod (j ++ con 1) 10 $ (4, [k === n], i_j_constraint 0 9)
   -- Off by one (i + 1 % 9)
   ,check SolveIneq $ withKIsMod (i ++ con 1) 9 $ withNIsMod (j ++ con 1) 9 $ (5, [k === n], i_j_constraint 0 9)
   
   -- The "nightmare" example from the Omega Test paper:
   ,check ImpossibleIneq (6,[],leq [con 27, 11 ** i ++ 13 ** j, con 45] &&& leq [con (-10), 7 ** i ++ (-9) ** j, con 4])

   -- Solution is: i = 0, j = 0, k = 0
   ,check (SolveEq $ answers [(i,0),(j,0),(k,0)])
                  (7, [con 0 === i ++ j ++ k,
                       con 0 === 5 ** i ++ 4 ** j ++ 3 ** k,
                       con 0 === i ++ 6 ** j ++ 2 ** k]
                    , [con 1 >== i ++ 3 ** j ++ k,
                       con (-4) <== (-5) ** i ++ 2 ** j ++ k,
                       con 0 >== 4 ** i ++ (-7) ** j ++ (-13) ** k])

   -- Solution is i = 0, j = 0, k = 4
   ,check (SolveEq $ answers [(i,0),(j,0),(k,4)])
                  (8, [con 4 === i ++ j ++ k,
                       con 12 === 5 ** i ++ 4 ** j ++ 3 ** k,
                       con 8 === i ++ 6 ** j ++ 2 ** k]
                    , [con 5 >== i ++ 3 ** j ++ k,
                       con 3 <== (-5) ** i ++ 2 ** j ++ k,
                       con (-52) >== 4 ** i ++ (-7) ** j ++ (-13) ** k])

   -- Solution is: i = 0, j = 5, k = 4, but
   -- this can't be determined from the equalities alone.
   ,check SolveIneq (9, [con 32 === 4 ** i ++ 4 ** j ++ 3 ** k,
                       con 17 === i ++ j ++ 3 ** k,
                       con 54 === 10 ** i ++ 10 ** j ++ k]
                    , [3 ** i ++ 8 ** j ++ 5 ** k >== con 60,
                       i ++ j ++ 3 ** k >== con 17,
                       5 ** i ++ j ++ 5 ** k >== con 25])

   -- If we have (solution: 1,2):
   --   5 <= 5y - 4x <= 7
   --   9 <= 3y + 4x <= 11
   -- Bounds on x:
   --   Upper: 4x <= 5y - 5, 4x <= 11 - 3y
   --   Lower: 5y - 7 <= 4x, 9 - 3y <= 4x
   -- Dark shadow of x includes:
   --   4(11 - 3y) - 4(9 - 3y) >= 9, gives 8 >= 9.
   -- Bounds on y:
   --   Upper: 5y <= 7 + 4x, 3y <= 11 - 4x
   --   Lower: 5 + 4x <= 5y, 9 - 4x <= 3y
   -- Dark shadow of y includes:
   --   5(7 + 4x) - 5(5 + 4x) >= 16, gives 10 >= 16
   -- So no solution to dark shadow, either way!
   ,check SolveIneq (10, [], leq [con 5, 5 ** i ++ (-4) ** j, con 7] &&& leq [con 9, 3 ** i ++ 4 ** j, con 11])


   ,safeParTest 100 True (0,10) [i]
   ,safeParTest 120 False (0,10) [i,i ++ con 1]
   ,safeParTest 140 True (0,10) [2 ** i, 2 ** i ++ con 1]
  ]
  where
    -- Given some indexes using "i", this function checks whether these can
    -- ever overlap within the bounds given, and matches this against
    -- the expected value; True for safe, False for unsafe.
    safeParTest :: Int -> Bool -> (Integer,Integer) -> [[(Int,Integer)]] -> Test
    safeParTest ind expSafe (low, high) usesI = TestCase $
      (if expSafe
        then assertEqual ("testIndexes " ++ show ind ++ " should be safe (unsolveable)") []
        else assertNotEqual ("testIndexes " ++ show ind ++ " should be solveable") []
      ) 
        $ findSolveable $ zip3 [ind..] (equalityCombinations) (repeat constraint)
      where
        changeItoJ (1,n) = (2,n)
        changeItoJ x = x
      
        usesJ = map (map changeItoJ) usesI
        
        constraint = i_j_constraint low high
        
        equalityCombinations :: [[HandyEq]]
        equalityCombinations = map (\(lhs,rhs) -> [lhs === rhs]) $ product2 (usesI,usesJ)
  
      
    findSolveable :: [(Int, [HandyEq], [HandyIneq])] -> [(Int, [HandyEq], [HandyIneq])]
    findSolveable = filter isSolveable
    
    isSolveable :: (Int, [HandyEq], [HandyIneq]) -> Bool
    isSolveable (ind, eq, ineq) = isJust $ (uncurry solveProblem) (makeConsistent eq ineq)
    
    isMod :: [(Int,Integer)] -> [(Int,Integer)] -> Integer -> ([HandyEq], [HandyIneq])
    isMod var@[(ind,1)] alpha divisor = ([alpha_minus_div_sigma === var], leq [con 0, alpha_minus_div_sigma, con $ divisor - 1])
      where
        alpha_minus_div_sigma = alpha ++ (negate divisor) ** sigma
        sigma :: [(Int, Integer)]
        sigma = [(ind+1,1)]
    
    -- | Adds both k and m to the equation!
    withKIsMod :: [(Int,Integer)] -> Integer -> (Int, [HandyEq], [HandyIneq]) -> (Int, [HandyEq], [HandyIneq])
    withKIsMod alpha divisor (ind,eq,ineq) = let (eq',ineq') = isMod k alpha divisor in (ind,eq ++ eq',ineq ++ ineq')

    -- | Adds both n and p to the equation!
    withNIsMod :: [(Int,Integer)] -> Integer -> (Int, [HandyEq], [HandyIneq]) -> (Int, [HandyEq], [HandyIneq])
    withNIsMod alpha divisor (ind,eq,ineq) = let (eq',ineq') = isMod n alpha divisor in (ind,eq ++ eq',ineq ++ ineq')

-- | Given one mapping and a second mapping, gives a function that converts the indexes
-- from one to the indexes of the next.  If any of the keys in the map don't match
-- (i.e. if (keys m0 /= keys m1)) Nothing will be returned

generateMapping :: TestMonad m r => String -> VarMap -> VarMap -> m [(CoeffIndex,CoeffIndex)]
generateMapping msg m0 m1
  = do testEqual ("Keys in variable mapping " ++ msg) (Map.keys m0') (Map.keys m1')
       return $ Map.elems $ zipMap mergeMaybe m0' m1'
  where
    m0' = Map.mapKeys (fmapFlattenedExp canonicalise) m0
    m1' = Map.mapKeys (fmapFlattenedExp canonicalise) m1

-- | Given a forward mapping list, translates equations across
translateEquations :: forall m r. TestMonad m r =>
  [(CoeffIndex,CoeffIndex)] -> (EqualityProblem, InequalityProblem) -> m (EqualityProblem, InequalityProblem)
translateEquations mp (eq,ineq)
  = do testEqual "translateEquations mapping not one-to-one" (sort $ map fst mp) (sort $ map snd mp)
       testCompareCustom "translateEquations input not square" (>=) 1 $ length $ nub $ map (snd . bounds) $ eq ++ ineq
       eq' <- mapM swapColumns eq
       ineq' <- mapM swapColumns ineq
       return (eq', ineq')
  where
    swapColumns :: Array CoeffIndex Integer -> m (Array CoeffIndex Integer)
    swapColumns arr
      = do swapped <- mapM swapColumns' $ assocs arr
           check arr swapped
           return $ simpleArray swapped
      where
        swapColumns' :: (CoeffIndex,Integer) -> m (CoeffIndex,Integer)
        swapColumns' (0,v) = return (0,v) -- Never swap the units column
        swapColumns' (x,v)
          = case find ((== x) . fst) mp of
              Just (_,y) -> return (y,v)
              Nothing -> testFailure "Could not find column to swap to"  >> return undefined
    
    check :: Show a => a -> [(CoeffIndex,Integer)] -> m ()
    check x ies = if length ies == 1 + maximum (map fst ies) then return () else
       testFailure $ "Error in translateEquations, not all indexes present after swap: " ++ show ies
         ++ " value beforehand was: " ++ show x ++ " mapping was: " ++ show mp

instance (ShowOccam a, Show b) => ShowOccam (a,b) where
  showOccamM (x,y) = showOccamM x >> tell [show y]

type Problem = (((A.Expression, [ModuloCase]), (A.Expression, [ModuloCase])), VarMap, (EqualityProblem, InequalityProblem))

-- | Asserts that the two problems are equivalent, once you take into account the potentially different variable mappings
assertEquivalentProblems :: forall m r. (TestMonad m r) => String -> [Problem] -> [Problem] -> m ()
assertEquivalentProblems title exp act
  = do testEqualCustomShow (showListCustom $ showPairCustom showLabel showLabel) "Label sets not equal"
         (map fst3 $ sortByLabels exp) (map fst3 $ sortByLabels act)
       transformed <- mapM (uncurry $ transform $ showPairCustom showLabel showLabel) $ zip (sortByLabels exp) (sortByLabels act)
--       let transformedSortedZipped = map (transformPair id (zip . transformPair sortProblem sortProblem . unzip)) $ transformed
       -- To give a more useful error on large problems we compare each item individually:   
       mapM_ test $ zip [0..] $ map (transformPair (\(e,a) -> showOccam e ++ " = " ++ showOccam a) id) transformed
       testEqual (title ++ " Problems were not the same size") (length exp) (length act)
  where
    test :: (Int, (String, ((EqualityProblem, InequalityProblem), (EqualityProblem, InequalityProblem)))) -> m ()
    test (n, (l, (eps, aps))) = testEqualCustomShow showProblem (title ++ " " ++ l ++ " #" ++ show n) eps aps
  
    showLabel :: (A.Expression, [ModuloCase]) -> String
    showLabel = showPairCustom showOccam show
  
    showFunc :: (Int, [(EqualityProblem, InequalityProblem)]) -> String
    showFunc = showPairCustom show $ showListCustom $ showProblem
  
    fst3 :: (a,b,c) -> a
    fst3 (a,_,_) = a
  
    sortByLabels :: [Problem] -> [Problem]
    sortByLabels = sortBy (comparing fst3) . map (\(es,b,c) -> (sortPair es, b, c))
    
    sortPair :: Ord a => (a,a) -> (a, a)
    sortPair (x,y) | x <= y    = (x,y)
                   | otherwise = (y,x)

    sortP :: (EqualityProblem, InequalityProblem) -> (EqualityProblem, InequalityProblem)
    sortP (eq,ineq) = (sort $ map normaliseEquality eq, sort ineq)

    transform :: Eq label => (label -> String) ->
                 (label, VarMap, (EqualityProblem, InequalityProblem)) ->
                 (label, VarMap, (EqualityProblem, InequalityProblem)) ->
                       m ( label, ((EqualityProblem, InequalityProblem), (EqualityProblem, InequalityProblem)))
    transform s (el, vmexp, (e_eq, e_ineq)) (al, vmact, (a_eq, a_ineq))
      = do testEqualCustomShow s "Labels did not match" el al
           mapping <- generateMapping (showListCustom showOccam $ sort . nub $ map (fst . fst . fst3) exp ++ map (fst . snd . fst3) exp) (vmexp) (vmact)
           translatedExp <- translateEquations mapping (resize e_eq, resize e_ineq)
           return (el, (sortP translatedExp, sortP (resize a_eq, resize a_ineq)))
      where
        size = maximum $ map (snd . bounds) $ concat [e_eq, e_ineq, a_eq, a_ineq]

        resize :: [Array CoeffIndex Integer] -> [Array CoeffIndex Integer]
        resize = map (makeArraySize (0, size) 0)

  
        
    pairPairs (xa,ya) (xb,yb) = ((xa,xb), (ya,yb))
    
    sortProblem :: [(EqualityProblem, InequalityProblem)] -> [(EqualityProblem, InequalityProblem)]
    sortProblem = sort

-- QuickCheck tests for Omega Test:
-- The idea is to begin with a random list of integers, representing answers.
-- Combine this with a randomly generated matrix of coefficients for equalities
-- and the similar for inequalities.  Correct all the unit coefficients such that 
-- the equalities are true, and the inequalities should all resolve such that
-- LHS = RHS (and therefore they will be pruned out)

-- | We want to generate a solveable equation.  Expressing our N equations as a matrix A (size: NxN),
-- we get: A . x = b, where b is our solution.  The equations are solveable iff x = inv(A) . b
-- Or expressed another way, the equations are solveable iff A is nonsingular;
-- see http://mathworld.wolfram.com/LinearSystemofEquations.html  A is singular if it
-- has determinant zero, therefore A is non-singular if the determinant is non-zero.
-- See http://mathworld.wolfram.com/Determinant.html for this.
--
-- At first I tried to simply check the determinant of a randomly generated matrix.
-- I implemented the standard naive algorithm, which is O(N!).  Eeek!  Reading the maths
-- more, a quicker way to do the determinant of a matrix M is to decompose it into
-- M = LU (where L is lower triangular, and U is upper triangular).  Once you have
-- done this, you can use det M = det (LU) = (det L) . (det U) (from the Determinant page)
-- This is easier because det (A) where A is triangular, is simply the product
-- of its diagonal elements (see http://planetmath.org/encyclopedia/TriangularMatrix.html).
--
-- However, we don't need to do this the hard way.  We just want to generate a matrix M
-- where its determinant is non-zero.  If we imagine M = LU, then (det M) is non-zero
-- as long as (det L) is non-zero AND (det U) is non-zero.  In turn, det L and det U are
-- non-zero as long as all their diagonal elements are non-zero.  Therefore we just
-- need to randomly generate L and U (such that the diagonal elements are all non-zero)
-- and do M = LU.
--
-- Note that we should not take the shortcut of using just L or just U.  This would
-- lead to trivially solveable linear equations, which would not test our algorithm well!
generateInvertibleMatrix :: Int -> Gen [[Integer]]
generateInvertibleMatrix size
  = do u <- genUpper
       l <- genLower
       return $ l `multMatrix` u
  where
    ns = [0 .. size - 1]

    -- | From http://mathworld.wolfram.com/MatrixMultiplication.html:
    -- To multiply two square matrices of size N:
    -- c_ik = sum (j in 0 .. N-1) (a_ij . b_jk)
    -- Note that we begin our indexing at zero, because that's how !! works.
    multMatrix a b = [[sum [((a !! i) !! j) * ((b !! j) !! k) | j <- ns] | k <- ns] | i <- ns]

    genUpper :: Gen [[Integer]]
    genUpper = mapM sequence [[
      case i `compare` j of
        EQ -> oneof [choose (-10,-1),choose (1,10)]
        LT -> return 0
        GT -> choose (-10,10)
       | i <- ns] |j <- ns]

    genLower :: Gen [[Integer]]
    genLower = mapM sequence [[
      case i `compare` j of
        EQ -> oneof [choose (-10,-1),choose (1,10)]
        GT -> return 0
        LT -> choose (-10,10)
       | i <- ns] |j <- ns]       

-- | Given a solution, and the coefficients, work out the result.
-- Effectively the dot-product of the two lists.
calcUnits :: [Integer] -> [Integer] -> Integer
calcUnits a b = sum $ zipWith (*) a b

-- | Given the solution for an equation (values of x_1 .. x_n), generates 
-- equalities and inequalities.  The equalities will all be true and consistent,
-- the inequalities will all turn out to be equal.  That is, when the inequalities
-- are resolved, the LHS will equal 0.  Therefore we can generate the inequalities
-- using the same method as equalities.  Also, the equalities are assured to be 
-- distinct.  If they were not distinct (one could be transformed into another by scaling)
-- then the equation set would be unsolveable.
generateEqualities :: [Integer] -> Gen (EqualityProblem, InequalityProblem)
generateEqualities solution = do eqCoeffs <- generateInvertibleMatrix num_vars
                                 ineqCoeffs <- generateInvertibleMatrix num_vars
                                 return (map mkCoeffArray eqCoeffs, map mkCoeffArray ineqCoeffs)
  where
    num_vars = length solution
    mkCoeffArray coeffs = arrayise $ (negate $ calcUnits solution coeffs) : coeffs

-- | The input to a test that will have an exact solution after the equality problems have been
-- solved.  All the inequalities will be simplified to 0 = 0.  The answers to the equation are
-- in the map.
newtype OmegaTestInput = OMI (Map.Map CoeffIndex Integer,(EqualityProblem, InequalityProblem)) deriving (Show)

-- | Generates an Omega test problem with between 1 and 10 variables (incl), where the solutions
-- are numbers between -20 and + 20 (incl).
generateProblem :: Gen (Map.Map CoeffIndex Integer,(EqualityProblem, InequalityProblem))
generateProblem = choose (1,10) >>= (\n -> replicateM n $ choose (-20,20)) >>=
                    (\ans -> seqPair (return $ makeAns (zip [1..] ans),generateEqualities ans))
  where
    makeAns :: [(Int, Integer)] -> Map.Map CoeffIndex Integer
    makeAns = Map.fromList

instance Arbitrary OmegaTestInput where
  arbitrary = generateProblem >>* OMI

qcOmegaEquality :: [LabelledQuickCheckTest]
qcOmegaEquality = [("Omega Test Equality Solving", scaleQC (40,200,2000,10000) (runQCTest . prop))]
  where
    prop :: OmegaTestInput -> QCProp
    prop (OMI (ans,(eq,ineq))) = omegaCheck actAnswer
      where
        actAnswer = solveConstraints (defaultMapping $ Map.size ans) eq ineq
        -- We use Map.assocs because pshow doesn't work on Maps
        omegaCheck (Just (vm,ineqs)) = (True *==* all (all (== 0) . elems) ineqs)
          *&&* ((Map.assocs ans) *==* (Map.assocs $ getCounterEqs vm))
        omegaCheck Nothing = testFailure ("Found Nothing while expecting answer: " ++ show (eq,ineq))

-- | A randomly mutated problem ready for testing the inequality pruning.
-- The first part is the input to the pruning, and the second part is the expected result;
-- the remaining inequalities, preceding by a list of equalities.
type MutatedProblem =
  (InequalityProblem
  ,Maybe ([EqualityConstraintEquation],InequalityProblem))

-- | The type for inside the function; easier to work with since it can't be
-- inconsistent until the end.
type MutatedProblem' =
  (InequalityProblem
  ,[EqualityConstraintEquation]
  ,InequalityProblem)

-- | Given a distinct inequality list, mutates each one at random using one of these mutations:
-- * Unchanged
-- * Generates similar but redundant equations
-- * Generates its dual (to be transformed into an equality equation)
-- * Generates an inconsistent partner (rare - 20% chance of existing in the returned problem).
-- The equations passed in do not have to be consistent, merely unique and normalised.
-- Returns the input, and the expected output.
mutateEquations :: InequalityProblem -> Gen MutatedProblem
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

    mutate :: InequalityConstraintEquation -> Gen MutatedProblem'
    mutate ineq = oneof
                    [
                      return ([ineq],[],[ineq])
                     ,addRedundant ineq
                     ,return $ addDual ineq
                    ]

    addDual :: InequalityConstraintEquation -> MutatedProblem'
    addDual eq = ([eq,neg],[eq],[]) where neg = amap negate eq

    addRedundant :: InequalityConstraintEquation -> Gen MutatedProblem'
    addRedundant ineq = do i <- choose (1,5) -- number of redundant equations to add
                           newIneqs <- replicateM i addRedundant'
                           return (ineq : newIneqs, [], [ineq])
                             where
                               -- A redundant equation is one with a bigger unit coefficient:
                               addRedundant' = do n <- choose (1,100)
                                                  return $ ineq // [(0,n + (ineq ! 0))]

-- | Puts an equality into normal form.  This is where the first non-zero coefficient is positive.
-- If all coefficients are zero, it doesn't matter (it will be equal to its negation)
normaliseEquality :: EqualityConstraintEquation -> EqualityConstraintEquation
normaliseEquality eq = case listToMaybe $ filter (/= 0) $ elems eq of
                         Nothing -> eq -- all zeroes
                         Just x -> amap (* (signum x)) eq

newtype OmegaPruneInput = OPI MutatedProblem deriving (Show)

instance Arbitrary OmegaPruneInput where
  arbitrary = ((generateProblem >>* snd)  >>= (return . snd) >>= mutateEquations) >>* OPI

qcOmegaPrune :: [LabelledQuickCheckTest]
qcOmegaPrune = [("Omega Test Pruning", scaleQC (100,1000,10000,50000) prop)]
  where
    --We perform the map assocs because we can't compare arrays using *==*
    -- (toConstr fails in the pretty-printing!).
    prop (OPI (inp,out)) = True
    {-
      case out of
        Nothing -> Nothing *==* result
        Just (expEq,expIneq) ->
          case result of
            Nothing -> mkFailResult $ "Expected success but got failure: " ++ pshow (inp,out)
            Just (actEq,actIneq) ->
              (sort (map assocs expIneq) *==* sort (map assocs actIneq))
              *&&* ((sort $ map normaliseEquality expEq) *==* (sort $ map normaliseEquality actEq))
      where
        result = undefined -- TODO replace solveAndPrune: solveProblem [] inp
    -}
    
vioqcTests :: Int -> IO (Test, [LabelledQuickCheckTest])
vioqcTests v
  = seqPair
      (liftM (TestLabel "ArrayUsageCheckTest" . TestList) $ sequence $
        map return [
          testArrayCheck
         ,testIndexes
         ,testMakeEquations
         ]
        ++ map (automaticTest FrontendOccam v)
         ["testcases/automatic/usage-check-1.occ.test"
         ,"testcases/automatic/usage-check-2.occ.test"
         ,"testcases/automatic/usage-check-3.occ.test"
         ,"testcases/automatic/usage-check-4.occ.test"
         ,"testcases/automatic/usage-check-5.occ.test"
         ,"testcases/automatic/usage-check-6.occ.test"
         ,"testcases/automatic/usage-check-7.occ.test"
         ,"testcases/automatic/usage-check-8.occ.test"
         ,"testcases/automatic/usage-check-9.occ.test"
         ,"testcases/automatic/usage-check-10.occ.test"
         ]
      ,return $ qcOmegaEquality ++ qcOmegaPrune ++ qcTestMakeEquations)



