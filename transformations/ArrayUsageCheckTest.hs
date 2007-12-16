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
import Test.QuickCheck


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


testIndexes :: Test
testIndexes = TestList
  [
  
    easilySolved (0, [i === con 7], [])
   ,easilySolved (1, [2 ** i === con 12], [])
    --should fail:
   ,notSolveable (2, [i === con 7],[i <== con 5])
   
   -- Can i = j?
   ,notSolveable (3, [i === j], i_j_constraint 0 9)

   -- TODO need to run the below exampls on a better test (they are not "easily" solved):
   
   -- Can (j + 1 % 10 == i + 1 % 10)?
   ,neverSolveable $ withKIsMod (i ++ con 1) 10 $ withNIsMod (j ++ con 1) 10 $ (4, [k === n], i_j_constraint 0 9)
   -- Off by one (i + 1 % 9)
   ,hardSolved $ withKIsMod (i ++ con 1) 9 $ withNIsMod (j ++ con 1) 9 $ (5, [k === n], i_j_constraint 0 9)
   
   -- The "nightmare" example from the Omega Test paper:
   ,neverSolveable (6,[],leq [con 27, 11 ** i ++ 13 ** j, con 45] &&& leq [con (-10), 7 ** i ++ (-9) ** j, con 4])
   
   ,safeParTest 100 True (0,10) [i]
   ,safeParTest 120 False (0,10) [i,i ++ con 1]
   ,safeParTest 140 True (0,10) [2 ** i, 2 ** i ++ con 1]
   
   
   --TODO tidy up the tests and add this example that once failed the QuickCheck tests:
   
   --OMI ([array (0,3) [(0,0),(1,-1),(2,0),(3,0)],array (0,3) [(0,5),(1,0),(2,-1),(3,0)],array (0,3) [(0,4),(1,0),(2,0),(3,-1)]],([array (0,3) [(0,-32),(1,4),(2,4),(3,3)],array (0,3) [(0,-17),(1,1),(2,1),(3,3)],array (0,3) [(0,-54),(1,10),(2,10),(3,1)]],[array (0,3) [(0,-60),(1,3),(2,8),(3,5)],array (0,3) [(0,-60),(1,9),(2,4),(3,10)],array (0,3) [(0,-25),(1,5),(2,1),(3,5)]]))
      
   ,TestCase $ assertStuff "testIndexes makeEq"
     (Right (Map.empty,(uncurry makeConsistent) (doubleEq [con 0 === con 1],leq [con 0,con 0,con 7] &&& leq [con 0,con 1,con 7]))) $
     makeEquations [intLiteral 0, intLiteral 1] (intLiteral 7)
   ,TestCase $ assertStuff "testIndexes makeEq 2"
     (Right (Map.singleton "i" 1,(uncurry makeConsistent) (doubleEq [i === con 3],leq [con 0,con 3,con 7] &&& leq [con 0,i,con 7]))) $
     makeEquations [exprVariable "i",intLiteral 3] (intLiteral 7)
     
   ,TestCase $ assertCounterExampleIs "testIndexes testVarMapping" (Map.fromList [(1,7)])
     $ makeConsistent [i === con 7] []
  ]
  where
    -- TODO comment these functions and rename the latter one
    doubleEq = concatMap (\(Eq e) -> [Eq e,Eq $ negateVars e])
    assertStuff title x y = assertEqual title (munge x) (munge y)
      where
        munge = transformEither id (transformPair id (transformPair sort sort))
    
    assertCounterExampleIs title counterEq (eq,ineq)
      = assertCompareCustom title equivEq (Just counterEq) ((solveAndPrune eq ineq) >>* (getCounterEqs . fst))
      where
        equivEq (Just xs) (Just ys) = xs == ys
        equivEq Nothing Nothing = True
        equivEq _ _ = False

    
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
  
      
    --TODO clear up this mess of easilySolved/hardSolved helper functions
    
    findSolveable :: [(Int, [HandyEq], [HandyIneq])] -> [(Int, [HandyEq], [HandyIneq])]
    findSolveable = filter isSolveable
    
    isSolveable :: (Int, [HandyEq], [HandyIneq]) -> Bool
    isSolveable (ind, eq, ineq) = isJust $ (uncurry solveAndPrune) (makeConsistent eq ineq)
  
    easilySolved :: (Int, [HandyEq], [HandyIneq]) -> Test
    easilySolved (ind, eq, ineq) = TestCase $
      let ineq' = (uncurry solveAndPrune) (makeConsistent eq ineq) in
      case ineq' of
        Nothing -> assertFailure $ "testIndexes " ++ show ind ++ " expected to pass (solving+pruning) but failed; problem: " ++ show (eq,ineq)
        Just (_,ineq'') ->
          if numVariables ineq'' <= 1
            then return ()
            -- Until we put in the route from original to mapped variables,
            -- we can't give a useful test failure here:
            else assertFailure $ "testIndexes " ++ show ind ++ " more than one variable left after solving"

    hardSolved :: (Int, [HandyEq], [HandyIneq]) -> Test
    hardSolved (ind, eq, ineq) = TestCase $
      assertBool ("testIndexes " ++ show ind) $ isJust $ 
        (transformMaybe snd . uncurry solveAndPrune) (makeConsistent eq ineq) >>= (pruneAndCheck . fmElimination)

    notSolveable :: (Int, [HandyEq], [HandyIneq]) -> Test
    notSolveable (ind, eq, ineq) = TestCase $ assertEqual ("testIndexes " ++ show ind) Nothing $
      (transformMaybe snd . uncurry solveAndPrune) (makeConsistent eq ineq) >>* ((<= 1) . numVariables)


    neverSolveable :: (Int, [HandyEq], [HandyIneq]) -> Test
    neverSolveable (ind, eq, ineq) = TestCase $ assertEqual ("testIndexes " ++ show ind) Nothing $
      (transformMaybe snd . uncurry solveAndPrune) (makeConsistent eq ineq) >>= (pruneAndCheck . fmElimination)

    
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
    
    makeConsistent :: [HandyEq] -> [HandyIneq] -> (EqualityProblem, InequalityProblem)
    makeConsistent eqs ineqs = (map ensure eqs', map ensure ineqs')
      where
        eqs' = map (\(Eq e) -> e) eqs
        ineqs' = map (\(Ineq e) -> e) ineqs
      
        ensure = accumArray (+) 0 (0, largestIndex)
        largestIndex = maximum $ map (maximum . map fst) $ eqs' ++ ineqs'
        
-- QuickCheck tests for Omega Test:
-- The idea is to begin with a random list of integers, representing transformed y_i variables.
-- This will be the solution.  Feed this into a random list of inequalities.  The inequalities do
-- not have to be true; they merely have to exist.  Then slowly transform 


--TODO Allow zero coefficients (but be careful we don't
-- produce unsolveable equations, e.g. where an equation is all zeroes, or a_3 is zero in all of them)

-- | Generates a list of random numbers of the given size, where the numbers are all co-prime
-- (their GCD is one).  This is so they can be used as normalised coefficients in a linear equation.
coprimeList :: Int -> Gen [Integer]
coprimeList size = do non_normal <- replicateM size $ oneof [choose (-100,-1), choose (1,100)]
                      return $ map (\x -> x `div` (mygcdList non_normal)) non_normal

-- | Generates a list of lists of co-prime numbers, where each list is distinct.
-- The returned list of lists will be square; N equations, each with N items
distinctCoprimeLists :: Int -> Gen [[Integer]]
distinctCoprimeLists size = distinctCoprimeLists' [] size
  where
    -- Since we generate positive and negative coefficients, we must check both that
    -- our generated list [3,-5,8,8] and its negation [-3,5,-8,-8] are not in the list.
    -- n is the number left to generate; size is still the "width" of the lists
    distinctCoprimeLists' :: [[Integer]] -> Int -> Gen [[Integer]]
    distinctCoprimeLists' result 0 = return result
    distinctCoprimeLists' soFar n = do next <- coprimeList size
                                       if (next `elem` soFar) || ((map negate next) `elem` soFar)
                                         then distinctCoprimeLists' soFar n -- Try again
                                         else distinctCoprimeLists' (soFar ++ [next]) (n - 1)

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
generateEqualities solution = do eqCoeffs <- distinctCoprimeLists num_vars
                                 ineqCoeffs <- distinctCoprimeLists num_vars
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



