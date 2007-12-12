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

module ArrayUsageCheck where

import Control.Monad.State
import Data.Array.IArray
import Data.List
import Data.Maybe

import qualified AST as A
import FlowGraph
import Utils

--TODO fix this tangle of code to make it work with the code at the bottom of the file

data Constraint = Equality [CoeffVar] Integer

type Problem = [Constraint]

data CoeffVar = CV { coeff :: Integer, var :: A.Variable }

type CoeffExpr = [CoeffVar]

--type IndicesUsed = Map.Map Variable [[

makeProblems :: [[CoeffExpr]] -> [Problem]
makeProblems indexLists = map checkEq zippedPairs
  where
    allPairs :: [([CoeffExpr],[CoeffExpr])]
    allPairs = [(a,b) | a <- indexLists, b <- indexLists]
    zippedPairs :: [[(CoeffExpr,CoeffExpr)]]
    zippedPairs = map (uncurry zip) allPairs
    
    checkEq :: [(CoeffExpr,CoeffExpr)] -> Problem
    checkEq = map checkEq'
    
    checkEq' :: (CoeffExpr, CoeffExpr) -> Constraint
    checkEq' (cv0,cv1) = Equality (cv0 ++ map negate cv1) 0
    
    negate :: CoeffVar -> CoeffVar
    negate cv = cv {coeff = - (coeff cv)}

makeProblem1Dim :: [CoeffExpr] -> [Problem]
makeProblem1Dim ces = makeProblems [[c] | c <- ces]

type CoeffIndex = Int
type EqualityConstraintEquation = Array CoeffIndex Integer
type EqualityProblem = [EqualityConstraintEquation]

-- Assumed to be >= 0
type InequalityConstraintEquation = Array CoeffIndex Integer
type InequalityProblem = [InequalityConstraintEquation]

type StIneq = StateT InequalityProblem Maybe

solveConstraints :: EqualityProblem -> InequalityProblem -> Maybe InequalityProblem
solveConstraints p ineq
  = case normalise p of
      Nothing -> Nothing
      Just p' -> case (runStateT (solve p') ineq) of
                   Nothing -> Nothing
                   Just (_,s) -> Just s
  where
    normalise :: EqualityProblem -> Maybe EqualityProblem
    normalise = mapM normalise' --Note the mapM; if any calls to normalise' fail, so will normalise
      where
        normalise' :: EqualityConstraintEquation -> Maybe EqualityConstraintEquation
        normalise' e = let g = foldl1 gcd (elems e) in
                       if (((e ! 0) `mod` g) /= 0) then Nothing else Just $ amap (\x -> x `div` g) e
    
    solve :: EqualityProblem -> StateT InequalityProblem Maybe EqualityProblem
    solve [] = return []
    solve p = (solveUnits p >>* removeRedundant) >>= liftF checkFalsifiable >>= solveNext >>= solve
  
    checkForUnit :: EqualityConstraintEquation -> Maybe CoeffIndex
--    checkForUnit [_] = Nothing
--    checkForUnit is = listToMaybe $ map fst $ filter (absVal1 . snd) $ zip [1..] (tail is) -- Use [1..] because we've chopped off the 0-index value
    checkForUnit = listToMaybe . map fst . filter (absVal1 . snd) . tail . assocs

  
    absVal1 :: Integer -> Bool
    absVal1 1 = True
    absVal1 (-1) = True
    absVal1 _ = False


    findFirstUnit :: EqualityProblem -> (Maybe (EqualityConstraintEquation,CoeffIndex),EqualityProblem)
    findFirstUnit [] = (Nothing,[])
    findFirstUnit (e:es) = case checkForUnit e of
                             Just ci -> (Just (e,ci),es)
                             Nothing -> let (me,es') = findFirstUnit es in (me,e:es')
                             

    substIn :: CoeffIndex -> Array CoeffIndex Integer -> EqualityProblem -> EqualityProblem
    substIn ind arr = map substIn'
      where
        substIn' eq = changeAllButOneDifferent (ind,0) id $ arrayZipWith (+) eq (amap (* (eq ! ind)) arr)

    solveUnits :: EqualityProblem -> StateT InequalityProblem Maybe EqualityProblem
    solveUnits p = case findFirstUnit p of
                      (Nothing,p') -> return p' -- p' should equal p anyway
                      (Just (eq,ind),p') -> modify change >> solveUnits (change p')
                        where
                          change = substIn ind (arrayMapWithIndex (curry $ negateOthers ind) eq)
    
    negateOthers :: CoeffIndex -> (CoeffIndex,Integer) -> Integer
    negateOthers match (ind,val) = if match == ind then 0 else negate val
    
    findSmallestAbsCoeff :: EqualityConstraintEquation -> CoeffIndex
    findSmallestAbsCoeff = fst. minimumBy (cmpAbsSnd) . filter ((/= 0) . snd) . tail . assocs
      where
        cmpAbsSnd :: (a,Integer) -> (a,Integer) -> Ordering
        cmpAbsSnd (_,x) (_,y) = compare (abs x) (abs y)

    solveNext :: EqualityProblem -> StateT InequalityProblem Maybe EqualityProblem
    solveNext [] = return []
    solveNext (e:es) = -- We transform the kth variable into sigma, effectively
                       -- So once we have x_k = ... (in terms of sigma) we add a_k * RHS
                       -- to all other equations, AFTER zeroing the a_k coefficient (so
                       -- that the multiple of sigma is added on properly)
                       modifyM_ (normalise . map alterEquation) >> (lift $ (normalise . map alterEquation) (e:es))
                         where
                           alterEquation :: EqualityConstraintEquation -> EqualityConstraintEquation
                           alterEquation eq = arrayZipWith (+) (eq // [(k,0)]) (amap (\x -> x * (eq ! k)) x_k_eq)
                           
                         
                           k = findSmallestAbsCoeff e
                           a_k = e ! k
                           m = (abs a_k) + 1
                           sign_a_k = signum a_k
                           x_k_eq = changeAllButOneDifferent (k,(- sign_a_k) * m) (\a_i -> sign_a_k * (a_i `mymod` m)) e
                         
                           -- I think this is probably equivalent to mod, but let's follow the maths:
                           mymod x y = x - (y * (floordivplushalf x y))
                           
                           -- This is floor (x/y + 1/2).  Probably a way to do it without reverting to float arithmetic:
                           floordivplushalf :: Integer -> Integer -> Integer
                           floordivplushalf x y = floor ((fromInteger x / fromInteger y) + (0.5 :: Double))

    changeAllButOneDifferent :: (IArray a e, IArray a e', Ix i) => (i,e') -> (e -> e') -> a i e -> a i e'
    changeAllButOneDifferent (specialI,specialE) f = arrayMapWithIndex f'
      where
        f' i e = if i == specialI then specialE else f e

    -- Removes all equations where the coefficients are all zero
    removeRedundant :: EqualityProblem -> EqualityProblem
    removeRedundant = mapMaybe (boolToMaybe (not . isRedundant))
      where
        isRedundant :: EqualityConstraintEquation -> Bool
        isRedundant = all (== 0) . elems
    

    -- Searches for all equations where only the a_0 coefficient is non-zero; this means the equation cannot be satisfied
    checkFalsifiable :: EqualityProblem -> Maybe EqualityProblem
    checkFalsifiable = boolToMaybe (not . any checkFalsifiable')
      where
        -- | Returns True if the equation is definitely unsatisfiable
        checkFalsifiable' :: EqualityConstraintEquation -> Bool
        checkFalsifiable' e = (e ! 0 /= 0) && (all (== 0) . tail . elems) e

