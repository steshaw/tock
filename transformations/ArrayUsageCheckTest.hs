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

module ArrayUsageCheckTest (qcTests) where

import Control.Monad.Identity
import Data.Array.IArray
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Prelude hiding ((**),fail)
import Test.HUnit
import Test.QuickCheck hiding (check)


import ArrayUsageCheck
import PrettyShow
import TestUtils hiding (m)
import Utils

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

(&&&) :: [HandyIneq] -> [HandyIneq] -> [HandyIneq]
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


makeConsistent :: [HandyEq] -> [HandyIneq] -> (EqualityProblem, InequalityProblem)
makeConsistent eqs ineqs = (map ensure eqs', map ensure ineqs')
  where
    eqs' = map (\(Eq e) -> e) eqs
    ineqs' = map (\(Ineq e) -> e) ineqs
      
    ensure = accumArray (+) 0 (0, largestIndex)
    largestIndex = maximum $ map (maximum . map fst) $ eqs' ++ ineqs'


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
          elimed = sapped >>= (return . snd) >>= (pruneAndCheck . fmElimination)
          testName = "check " ++ show s ++ " " ++ show ind

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
   ,check SolveIneq (6,[],leq [con 27, 11 ** i ++ 13 ** j, con 45] &&& leq [con (-10), 7 ** i ++ (-9) ** j, con 4])

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

   ,safeParTest 100 True (0,10) [i]
   ,safeParTest 120 False (0,10) [i,i ++ con 1]
   ,safeParTest 140 True (0,10) [2 ** i, 2 ** i ++ con 1]
   
   
   ,TestCase $ assertEquivalentProblems "testIndexes makeEq"
     (Map.empty,(uncurry makeConsistent) ([con 0 === con 1],leq [con 0,con 0,con 7] &&& leq [con 0,con 1,con 7]))
     =<< (checkRight $ makeEquations [intLiteral 0, intLiteral 1] (intLiteral 7))
     
   ,TestCase $ assertEquivalentProblems "testIndexes makeEq 3"
     (Map.singleton "i" 1,(uncurry makeConsistent) ([i === con 3],leq [con 0,con 3,con 7] &&& leq [con 0,i,con 7]))
     =<< (checkRight $ makeEquations [exprVariable "i",intLiteral 3] (intLiteral 7))
     
   ,TestCase $ assertEquivalentProblems "testIndexes makeEq 4"
     (Map.fromList [("i",1),("j",2)],(uncurry makeConsistent) ([i === j],leq [con 0,i,con 7] &&& leq [con 0,j,con 7]))
     =<< (checkRight $ makeEquations [exprVariable "i",exprVariable "j"] (intLiteral 7))     

   ,TestCase $ assertEquivalentProblems "testIndexes makeEq 5"
     (Map.fromList [("i",2),("j",1)],(uncurry makeConsistent) ([i === j],leq [con 0,i,con 7] &&& leq [con 0,j,con 7]))
     =<< (checkRight $ makeEquations [exprVariable "i",exprVariable "j"] (intLiteral 7))
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
    isSolveable (ind, eq, ineq) = isJust $ (uncurry solveAndPrune) (makeConsistent eq ineq)
    
    isMod :: [(Int,Integer)] -> [(Int,Integer)] -> Integer -> ([HandyEq], [HandyIneq])
    isMod var@[(ind,1)] alpha divisor = ([alpha_minus_div_sigma === var], leq [con 0, alpha_minus_div_sigma, con $ divisor - 1])
      where
        alpha_minus_div_sigma = alpha ++ (negate divisor) ** sigma
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
generateMapping :: Map.Map String CoeffIndex -> Map.Map String CoeffIndex -> Maybe [(CoeffIndex,CoeffIndex)]
generateMapping m0 m1 = if Map.keys m0 /= Map.keys m1 then Nothing else Just (Map.elems $ zipMap f m0 m1)
  where
    f (Just x) (Just y) = Just (x,y)
    f _ _ = Nothing
    -- More readable than liftM (,)  !

-- | Given a forward mapping list, translates equations across
translateEquations :: [(CoeffIndex,CoeffIndex)] -> (EqualityProblem, InequalityProblem) -> Maybe (EqualityProblem, InequalityProblem)
translateEquations mp = seqPair . transformPair (mapM swapColumns) (mapM swapColumns)
  where
    swapColumns :: Array CoeffIndex Integer -> Maybe (Array CoeffIndex Integer)
    swapColumns arr = liftM simpleArray $ mapM swapColumns' $ assocs arr
      where
        swapColumns' :: (CoeffIndex,Integer) -> Maybe (CoeffIndex,Integer)
        swapColumns' (0,v) = Just (0,v) -- Never swap the units column
        swapColumns' (x,v) = transformMaybe (\y -> (y,v)) $ transformMaybe fst $ find ((== x) . snd) mp

-- | Asserts that the two problems are equivalent, once you take into account the potentially different variable mappings
assertEquivalentProblems :: String -> (Map.Map String CoeffIndex, (EqualityProblem, InequalityProblem)) -> (Map.Map String CoeffIndex, (EqualityProblem, InequalityProblem)) -> Assertion
assertEquivalentProblems title exp act = assertEqual title translatedExp (Just $ sortP $ snd act)
  where
    sortP (eq,ineq) = (sort $ map normaliseEquality eq, sort ineq)
  
    translatedExp = ( generateMapping (fst exp) (fst act) >>= flip translateEquations (snd exp)) >>* sortP

checkRight :: Show a => Either a b -> IO b
checkRight (Left err) = assertFailure ("Not Right: " ++ show err) >> return undefined
checkRight (Right x) = return x

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

qcOmegaEquality :: [QuickCheckTest]
qcOmegaEquality = [scaleQC (40,200,2000,10000) prop]
  where
    prop (OMI (ans,(eq,ineq))) = omegaCheck actAnswer
      where
        actAnswer = solveConstraints (defaultMapping $ Map.size ans) eq ineq
        -- We use Map.assocs because pshow doesn't work on Maps
        omegaCheck (Just (vm,ineqs)) = (True *==* all (all (== 0) . elems) ineqs)
          *&&* ((Map.assocs ans) *==* (Map.assocs $ getCounterEqs vm))
        omegaCheck Nothing = mkFailResult ("Found Nothing while expecting answer: " ++ show (eq,ineq))

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

qcOmegaPrune :: [QuickCheckTest]
qcOmegaPrune = [scaleQC (100,1000,10000,50000) prop]
  where
    --We perform the map assocs because we can't compare arrays using *==*
    -- (toConstr fails in the pretty-printing!).
    prop (OPI (inp,out)) =
      case out of
        Nothing -> Nothing *==* result
        Just (expEq,expIneq) ->
          case result of
            Nothing -> mkFailResult $ "Expected success but got failure: " ++ pshow (inp,out)
            Just (actEq,actIneq) ->
              (sort (map assocs expIneq) *==* sort (map assocs actIneq))
              *&&* ((sort $ map normaliseEquality expEq) *==* (sort $ map normaliseEquality actEq))
      where
        result = pruneAndCheck inp

qcTests :: (Test, [QuickCheckTest])
qcTests = (TestList
 [
   testArrayCheck
  ,testIndexes
 ]
 ,qcOmegaEquality ++ qcOmegaPrune)



