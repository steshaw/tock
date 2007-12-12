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
  = normaliseEq p >>= (\p' -> execStateT (solve p') ineq)
  where
    -- | Normalises an equation by dividing all coefficients by their greatest common divisor.
    -- If the unit coefficient (a_0) doesn't divide by this GCD, Nothing will be returned
    -- (the constraints do not have an integer solution)
    normaliseEq :: EqualityProblem -> Maybe EqualityProblem
    normaliseEq = mapM normaliseEq' --Note the mapM; if any calls to normalise' fail, so will normalise
      where
        normaliseEq' :: EqualityConstraintEquation -> Maybe EqualityConstraintEquation
        normaliseEq' e | g == 0                  = Just e
                       | ((e ! 0) `mod` g) /= 0  = Nothing
                       | otherwise               = Just $ amap (\x -> x `div` g) e
                       where g = foldl1 mygcd (map abs $ tail $ elems e) -- g is the GCD of a_1 .. a_n (not a_0)

        mygcd :: Integer -> Integer -> Integer
        mygcd 0 0 = 0
        mygcd x y = gcd x y
    
    -- | Solves all equality problems in the given list.
    -- Will either succeed (Just () in the Error/Maybe monad) or fail (Nothing)
    solve :: EqualityProblem -> StateT InequalityProblem Maybe ()
    solve [] = return ()
    solve p = (solveUnits p >>* removeRedundant) >>= liftF checkFalsifiable >>= solveNext >>= solve
  
    checkForUnit :: EqualityConstraintEquation -> Maybe CoeffIndex
    checkForUnit = listToMaybe . map fst . filter coeffAbsVal1 . tail . assocs
      where
        coeffAbsVal1 :: (a, Integer) -> Bool
        coeffAbsVal1 (_,x) = (abs x) == 1

    findFirstUnit :: EqualityProblem -> (Maybe (EqualityConstraintEquation,CoeffIndex),EqualityProblem)
    findFirstUnit [] = (Nothing,[])
    findFirstUnit (e:es) = case checkForUnit e of
                             Just ci -> (Just (e,ci),es)
                             Nothing -> let (me,es') = findFirstUnit es in (me,e:es')
                             

    substIn :: CoeffIndex -> Array CoeffIndex Integer -> EqualityProblem -> EqualityProblem
    substIn k x_k_val = map substIn'
      where
        substIn' eq = (arrayZipWith (+) eq scaled_x_k_val) // [(k,0)]
          where
            scaled_x_k_val = amap (* (eq ! k)) x_k_val

    solveUnits :: EqualityProblem -> StateT InequalityProblem Maybe EqualityProblem
    solveUnits p
      = case findFirstUnit p of
          (Nothing,p') -> return p' -- p' should equal p anyway
          (Just (eq,ind),p') -> modify change >> ((lift $ normaliseEq $ change p') >>= solveUnits)
            where
              change = substIn ind (arrayMapWithIndex (modifyOthersZeroSpecific ind) eq)
              origVal = eq ! ind

              -- Zeroes a specific coefficient, modifies the others as follows:
              -- If the coefficient of x_k is 1, we need to negate the other coefficients
              -- to get its definition.  However, if the coefficient is -1, we don't need to
              -- do this.  For example, consider 2 + 3x_1 + x_2 - 4x_3 = 0.  In this case
              -- x_2 = -2 - 3x_1 + 4x_3; the negation of the original equation (ignoring x_2).
              -- If however, it was 2 + 3x_1 - x_2 - 4x_3 = 0 then x_2 = 2 + 3x_1 - 4x_3;
              -- that is, identical to the original equation if we ignore x_2.
              modifyOthersZeroSpecific :: CoeffIndex -> (CoeffIndex -> Integer -> Integer)
              modifyOthersZeroSpecific match ind
                | match == ind  = const 0 -- The specific value to zero out
                | origVal == 1  = negate  -- Original coeff was 1; negate
                | otherwise     = id      -- Original coeff was -1; don't do anything
    
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
                       modify (map alterEquation) >> (lift $ (normaliseEq . map alterEquation) (e:es))
                         where
                           alterEquation :: EqualityConstraintEquation -> EqualityConstraintEquation
                           alterEquation eq = arrayZipWith (+) (eq // [(k,0)]) (amap (\x -> x * (eq ! k)) x_k_eq)
                           
                         
                           k = findSmallestAbsCoeff e
                           a_k = e ! k
                           m = (abs a_k) + 1
                           sign_a_k = signum a_k
                           x_k_eq = amap (\a_i -> sign_a_k * (a_i `mymod` m)) e // [(k,(- sign_a_k) * m)]
                         
                           -- I think this is probably equivalent to mod, but let's follow the maths:
                           mymod x y = x - (y * (floordivplushalf x y))
                           
                           -- This is floor (x/y + 1/2).  Probably a way to do it without reverting to float arithmetic:
                           floordivplushalf :: Integer -> Integer -> Integer
                           floordivplushalf x y = floor ((fromInteger x / fromInteger y) + (0.5 :: Double))

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

