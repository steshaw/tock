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

-- | Solves all the constraints in the Equality Problem (taking them to be == 0),
-- and transforms the InequalityProblems appropriately.
-- TODO the function currently doesn't record the relation between the transformed variables
-- (e.g. sigma for x_k) and the original variables (x_k).  In order to feed back useful
-- information to the user, we should do this at some point in future.
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
                       where g = mygcdList (tail $ elems e) -- g is the GCD of a_1 .. a_n (not a_0)
    
    -- | Solves all equality problems in the given list.
    -- Will either succeed (Just () in the Error\/Maybe monad) or fail (Nothing)
    solve :: EqualityProblem -> StateT InequalityProblem Maybe ()
    solve [] = return ()
    solve p = (solveUnits p >>* removeRedundant) >>= liftF checkFalsifiable >>= solveNext >>= solve
  
    -- | Checks if any of the coefficients in the equation have an absolute value of 1.
    -- Returns either Just <the first such coefficient> or Nothing (there are no such coefficients in the equation).
    -- This function only looks at a_1 .. a_n.  That is, a_0 is ignored.
    checkForUnit :: EqualityConstraintEquation -> Maybe CoeffIndex
    checkForUnit = listToMaybe . map fst . filter coeffAbsVal1 . tail . assocs
      where
        coeffAbsVal1 :: (a, Integer) -> Bool
        coeffAbsVal1 (_,x) = (abs x) == 1

    -- | Finds the first unit coefficient (|a_k| == 1) in a set of equality constraints.
    -- Returns Nothing if there are no unit coefficients.  Otherwise it returns
    -- (Just (equation, indexOfUnitCoeff), otherEquations); that is, the specified equation is not
    -- present in the list of equations.
    findFirstUnit :: EqualityProblem -> (Maybe (EqualityConstraintEquation,CoeffIndex),EqualityProblem)
    findFirstUnit [] = (Nothing,[])
    findFirstUnit (e:es) = case checkForUnit e of
                             Just ci -> (Just (e,ci),es)
                             Nothing -> let (me,es') = findFirstUnit es in (me,e:es')
                             

    -- | Substitutes a value for x_k into an equation.  Given k, the value for x_k in terms
    -- of coefficients of other variables (let's call it x_k_val), it subsitutes this into
    -- all the equations in the list by adding x_k_val (scaled by a_k) to each equation and
    -- then zeroing out the a_k value.  Note that the (x_k_val ! k) value will be ignored;
    -- it should be zero, in any case (otherwise x_k would be defined in terms of itself!).
    substIn :: CoeffIndex -> Array CoeffIndex Integer -> EqualityProblem -> EqualityProblem
    substIn k x_k_val = map substIn'
      where
        substIn' eq = (arrayZipWith (+) eq scaled_x_k_val) // [(k,0)]
          where
            scaled_x_k_val = amap (* (eq ! k)) x_k_val

    -- | Solves (i.e. removes by substitution) all unit coefficients in the given list of equations.
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
    
    -- | Finds the coefficient with the smallest absolute value of a_1 .. a_n (i.e. not a_0)
    -- that is non-zero (i.e. zero coefficients are ignored).
    findSmallestAbsCoeff :: EqualityConstraintEquation -> CoeffIndex
    findSmallestAbsCoeff = fst . minimumBy cmpAbsSnd . filter ((/= 0) . snd) . tail . assocs
      where
        cmpAbsSnd :: (a,Integer) -> (a,Integer) -> Ordering
        cmpAbsSnd (_,x) (_,y) = compare (abs x) (abs y)

    -- | Solves the next equality and returns the new set of equalities.
    solveNext :: EqualityProblem -> StateT InequalityProblem Maybe EqualityProblem
    solveNext [] = return []
    solveNext (e:es) = -- We transform the kth variable into sigma, effectively
                       -- So once we have x_k = ... (in terms of sigma) we add a_k * RHS
                       -- to all other equations, AFTER zeroing the a_k coefficient (so
                       -- that the multiple of sigma is added on properly)
                       modify (map alterEquation) >> (lift $ (normaliseEq . map alterEquation) (e:es))
                         where
                           -- | Adds a scaled version of x_k_eq onto the current equation, after zeroing out
                           -- the a_k coefficient in the current equation.
                           alterEquation :: EqualityConstraintEquation -> EqualityConstraintEquation
                           alterEquation eq = arrayZipWith (+) (eq // [(k,0)]) (amap (\x -> x * (eq ! k)) x_k_eq)

                           k = findSmallestAbsCoeff e
                           a_k = e ! k
                           m = (abs a_k) + 1
                           sign_a_k = signum a_k
                           x_k_eq = amap (\a_i -> sign_a_k * (a_i `mymod` m)) e // [(k,(- sign_a_k) * m)]

                           -- I think this is probably equivalent to mod, but let's follow the maths:
                           mymod :: Integer -> Integer -> Integer
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


mygcd :: Integer -> Integer -> Integer
mygcd 0 0 = 0
mygcd x y = gcd x y

mygcdList :: [Integer] -> Integer
mygcdList [] = 0
mygcdList [x] = abs x
mygcdList (x:xs) = foldl mygcd x xs

-- | Prunes the inequalities.  It does what is described in section 2.3 of Pugh's ACM paper;
-- it removes redundant inequalities, fails (evaluates to Nothing) if it finds a contradiction
-- and turns any 2x + y <= 4, 2x + y >= 4 pairs into equalities.  The list of such equalities
-- (which may well be an empty list) and the remaining inequalities is returned.
-- As an additional step not specified in the paper, equations with no variables in them are checked
-- for consistency.  That is, all equations c >= 0 (where c is constant) are checked to 
-- ensure c is indeed >= 0, and those equations are removed.
pruneAndCheck :: InequalityProblem -> Maybe (EqualityProblem, InequalityProblem)
pruneAndCheck ineq = do let (opps,others) = splitEither $ groupOpposites $ map pruneGroup groupedIneq
                        (opps', eq) <- mapM checkOpposite opps >>* splitEither
                        checked <- mapM checkConstantEq (concat opps' ++ others) >>* catMaybes
                        return (eq, checked)
  where
    groupedIneq = groupBy (\x y -> EQ == coeffSort x y) $ sortBy coeffSort ineq

    coeffSort :: InequalityConstraintEquation -> InequalityConstraintEquation -> Ordering
    coeffSort x y = compare (tail $ elems x) (tail $ elems y)

    -- | Takes in a group of inequalities with identical a_1 .. a_n coefficients
    -- and returns the equation with the smallest unit coefficient.  Consider the standard equation:
    -- a_1.x_1 + a_2.x_2 .. a_n.x_n >= -a_0.  We want one equation with the maximum value of -a_0
    -- (this will be the strongest equation), which is therefore the minimum value of a_0.
    -- This therefore automatically removes duplicate and redundant equations.
    pruneGroup :: [InequalityConstraintEquation] -> InequalityConstraintEquation
    pruneGroup = minimumBy (\x y -> compare (x ! 0) (y ! 0))

    -- | Groups all equations with their opposites, if found.  Returns either a pair
    -- or a singleton.  O(N^2), but there shouldn't be that many inequalities to process (<= 10, I expect).
    -- Assumes equations have already been pruned, and that therefore for every unique a_1 .. a_n 
    -- set, there is only one equation.
    groupOpposites :: InequalityProblem -> [Either (InequalityConstraintEquation,InequalityConstraintEquation) InequalityConstraintEquation]
    groupOpposites [] = []
    groupOpposites (e:es) = case findOpposite e es of
                              Just (opp,rest) -> (Left (e,opp)) : (groupOpposites rest)
                              Nothing -> (Right e) : (groupOpposites es)

    findOpposite :: InequalityConstraintEquation -> [InequalityConstraintEquation] -> Maybe (InequalityConstraintEquation,[InequalityConstraintEquation])
    findOpposite _ [] = Nothing
    findOpposite target (e:es) | negTarget == (tail $ elems e) = Just (e,es)
                               | otherwise = case findOpposite target es of
                                               Just (opp,rest) -> Just (opp,e:rest)
                                               Nothing -> Nothing
      where
        negTarget = map negate $ tail $ elems target

    -- Checks if two "opposite" constraints are inconsistent.  If they are inconsistent, Nothing is returned.
    -- If they could be consistent, either the resulting equality or the inequalities are returned
    --
    -- If the equations are opposite, then setting z = sum (1 .. n) of a_n . x_n, the two equations must be:
    -- b + z >= 0
    -- c - z >= 0
    -- The choice of which equation is which is arbitrary.
    --
    -- It is easily seen that adding the two equations gives:
    --
    -- (b + c) >= 0
    -- 
    -- Therefore if (b + c) < 0, the equations are inconsistent.
    -- If (b + c) = 0, we can substitute into the original equations b = -c:
    --   -c + z >= 0
    --   c - z >= 0
    --   Rearranging both gives:
    --   z >= c
    --   z <= c
    --   This implies c = z.  Therefore we can take either of the original inequalities
    --   and treat them directly as equality (c - z = 0, and b + z = 0)
    -- If (b + c) > 0 then the equations are consistent but we cannot do anything new with them
    checkOpposite :: (InequalityConstraintEquation,InequalityConstraintEquation) ->
      Maybe (Either [InequalityConstraintEquation] EqualityConstraintEquation)
    checkOpposite (x,y) | (x ! 0) + (y ! 0) < 0   = Nothing
                        | (x ! 0) + (y ! 0) == 0  = Just $ Right x
                        | otherwise               = Just $ Left [x,y]

    -- The type of this function is quite confusing.  We want to use in the Maybe monad, so 
    -- the outer type indicates error; Nothing is an error.  Just x indicates non-failure,
    -- but x may either be Just y (keep the equation) or Nothing (remove it).  So the three
    -- possible returns are:
    -- * Nothing: Equation inconsistent
    -- * Just Nothing: Equation redundant
    -- * Just (Just e) : Keep equation.
    checkConstantEq :: InequalityConstraintEquation -> Maybe (Maybe InequalityConstraintEquation)
    checkConstantEq eq | all (== 0) (tail $ elems eq) = if (eq ! 0) >= 0 then Just Nothing else Nothing
                       | otherwise = Just $ Just eq

-- | Returns Nothing if there is definitely no solution, or (Just ineq) if 
-- further investigation is needed
solveAndPrune :: EqualityProblem -> InequalityProblem -> Maybe InequalityProblem
solveAndPrune [] ineq = return ineq
solveAndPrune eq ineq = solveConstraints eq ineq >>= pruneAndCheck >>= uncurry solveAndPrune

-- | Returns the number of variables (of x_1 .. x_n; x_0 is not counted)
-- that have non-zero coefficients in the given inequality problems.
numVariables :: InequalityProblem -> Int
numVariables ineq = length (nub $ concatMap findVars ineq)
  where
    findVars = map fst . filter ((/= 0) . snd) . tail . assocs
