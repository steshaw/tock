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

import Control.Monad.Error
import Control.Monad.State
import Data.Array.IArray
import Data.List
import qualified Data.Map as Map
import Data.Maybe

import qualified AST as A
import FlowGraph
import Utils

data FlattenedExp = Const Integer | Scale Integer A.Variable deriving (Eq,Show)

-- TODO probably want to take this into the PassM monad at some point
makeEquations :: [A.Expression] -> A.Expression -> Either String (Map.Map String Int, (EqualityProblem, InequalityProblem))
makeEquations es high = makeEquations' >>* (\(s,v,lh) -> (s,(pairEqs v, getIneqs lh v)))
  where
    makeEquations' :: Either String (Map.Map String Int, [(Integer,EqualityConstraintEquation)], (EqualityConstraintEquation, EqualityConstraintEquation))
    makeEquations' = do ((v,h),s) <- (flip runStateT) Map.empty $
                           do flattened <- lift (mapM flatten es)
                              eqs <- mapM makeEquation flattened
                              (1,high') <- (lift $ flatten high) >>= makeEquation 
                              return (eqs,high')
                        return (s,v,(amap (const 0) h, h))
                              
  
    -- Takes an expression, and transforms it into an expression like:
    -- (e_0 + e_1 + e_2) / d
    -- where d is a constant (non-zero!) integer, and each e_k
    -- is either a const, a var, const * var, or (const * var) % const [TODO].
    -- If the expression cannot be transformed into such a format, an error is returned
    flatten :: A.Expression -> Either String (Integer,[FlattenedExp])
    flatten (A.Literal _ _ (A.IntLiteral _ n)) = return (1,[Const (read n)])
    flatten (A.Dyadic m op lhs rhs) | op == A.Add   = combine' (flatten lhs) (flatten rhs)
                                    | op == A.Subtr = combine' (flatten lhs) (liftM (transformPair id (scale (-1))) $ flatten rhs)
                                    -- TODO Mul and Div
                                    | otherwise     = throwError ("Unhandleable operator found in expression: " ++ show op)
    flatten (A.ExprVariable _ v) = return (1,[Scale 1 v])
    flatten other = throwError ("Unhandleable item found in expression: " ++ show other)
    
    scale :: Integer -> [FlattenedExp] -> [FlattenedExp]
    scale sc = map scale'
      where
        scale' (Const n) = Const (n * sc)
        scale' (Scale n v) = Scale (n * sc) v
        
    combine' x y = do {x' <- x; y' <- y; combine x' y'}
    combine :: (Integer,[FlattenedExp]) -> (Integer,[FlattenedExp]) -> Either String (Integer,[FlattenedExp])
    combine (nx, ex) (ny, ey) = return $ (nx * ny, scale ny ex ++ scale nx ey)
 
    --TODO we need to handle lots more different expression types in future.
    -- For now we just handle dyadic +,-
  
    varIndex :: A.Variable -> StateT (Map.Map String Int) (Either String) Int
    varIndex (A.Variable _ (A.Name _ _ varName))
      = do st <- get
           let (st',ind) = case Map.lookup varName st of
                             Just val -> (st,val)
                             Nothing -> let newId = (1 + (maximum $ 0 : Map.elems st)) in
                                        (Map.insert varName newId st, newId)
           put st'
           return ind

    -- Pairs all possible combinations
    pairEqs :: [(Integer,EqualityConstraintEquation)] -> [EqualityConstraintEquation]
    pairEqs = filter (any (/= 0) . elems) . map (uncurry pairEqs') . product2 . mkPair
      where
        pairEqs' (nx,ex) (ny,ey) = arrayZipWith (-) (amap (* ny) ex) (amap (* nx) ey)
    
    getIneqs :: (EqualityConstraintEquation, EqualityConstraintEquation) -> [(Integer,EqualityConstraintEquation)] -> [InequalityConstraintEquation]
    getIneqs (low, high) = concatMap getLH
      where
        -- eq / sc >= low => eq - (sc * low) >= 0
        -- eq / sc <= high => (high * sc) - eq >= 0
      
        getLH :: (Integer,EqualityConstraintEquation) -> [InequalityConstraintEquation]
        getLH (sc, eq) = [eq `addEq` (scaleEq (-sc) low),(scaleEq sc high) `addEq` amap negate eq]
        
        addEq = arrayZipWith (+)
                
    makeEquation :: (Integer,[FlattenedExp]) -> StateT (Map.Map String Int) (Either String) (Integer,EqualityConstraintEquation)
    makeEquation (divisor, summedItems)
      = do eqs <- foldM makeEquation' Map.empty summedItems
           max <- maxVar
           return (divisor, mapToArray max eqs)
      where
        makeEquation' :: Map.Map Int Integer -> FlattenedExp -> StateT (Map.Map String Int) (Either String) (Map.Map Int Integer)
        makeEquation' m (Const n) = return $ add (0,n) m
        makeEquation' m (Scale n v) = varIndex v >>* (\ind -> add (ind, n) m)
        
        add :: (Int,Integer) -> Map.Map Int Integer -> Map.Map Int Integer
        add = uncurry (Map.insertWith (+))
        
        maxVar = get >>* (maximum . (0 :) . Map.elems)
    
    mapToArray :: (IArray a v, Num v, Num k, Ord k, Ix k) => k -> Map.Map k v -> a k v
    mapToArray highest = (\arr -> accumArray (+) 0 (0, highest) arr) . Map.assocs
    
type CoeffIndex = Int
type EqualityConstraintEquation = Array CoeffIndex Integer
type EqualityProblem = [EqualityConstraintEquation]

-- Assumed to be >= 0
type InequalityConstraintEquation = Array CoeffIndex Integer
type InequalityProblem = [InequalityConstraintEquation]

-- Maps the indexes of the current variables to an equation involving the original variables
type VariableMapping = Map.Map CoeffIndex EqualityConstraintEquation

-- | Given a maximum variable, produces a default mapping
defaultMapping :: Int -> VariableMapping
defaultMapping n = Map.fromList $ [ (i,array (0,n) [(j,if i == j then 1 else 0) | j <- [0 .. n]]) | i <- [0 .. n]]

-- | Adds a new variable to a map
addToMapping :: (CoeffIndex,EqualityConstraintEquation) -> VariableMapping -> VariableMapping
addToMapping (k,eq) old = Map.insert k trans old
  where
    trans = foldl1 (arrayZipWith (+)) $ map (\(k,v) -> scaleEq v (forceLookup k old)) $ assocs eq    
    forceLookup k m = fromJust $ Map.lookup k m
    
reverseEquality :: EqualityConstraintEquation -> VariableMapping -> EqualityConstraintEquation
reverseEquality eq mp = foldl1 (arrayZipWith (+)) $ map (\(k,v) -> scaleEq v (forceLookup k mp)) $ assocs eq
  where
    forceLookup k m = fromJust $ Map.lookup k m

scaleEq :: Integer -> EqualityConstraintEquation -> EqualityConstraintEquation
scaleEq n = amap (* n)

-- | Solves all the constraints in the Equality Problem (taking them to be == 0),
-- and transforms the InequalityProblems appropriately.  It also records
-- a variable mapping so that we can feed back the final answer to the user
solveConstraints :: VariableMapping -> EqualityProblem -> InequalityProblem -> Maybe (VariableMapping, InequalityProblem)
solveConstraints vm p ineq
  = normaliseEq p >>= (\p' -> execStateT (solve p') (vm,ineq))
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
    solve :: EqualityProblem -> StateT (VariableMapping, InequalityProblem) Maybe ()
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
    substIn :: CoeffIndex -> Array CoeffIndex Integer -> (VariableMapping, EqualityProblem) -> (VariableMapping, EqualityProblem)
    substIn k x_k_val = transformPair (addToMapping (k,x_k_val)) (map substIn')
      where
        substIn' eq = (arrayZipWith (+) eq scaled_x_k_val) // [(k,0)]
          where
            scaled_x_k_val = amap (* (eq ! k)) x_k_val

    -- | Solves (i.e. removes by substitution) all unit coefficients in the given list of equations.
    solveUnits :: EqualityProblem -> StateT (VariableMapping, InequalityProblem) Maybe EqualityProblem
    solveUnits p
      = case findFirstUnit p of
          (Nothing,p') -> return p' -- p' should equal p anyway
          (Just (eq,ind),p') -> modify change >> change' p' >>= liftF normaliseEq >>= solveUnits
            where
              change = substIn ind (arrayMapWithIndex (modifyOthersZeroSpecific ind) eq)
              change' p = do (mp,ineq) <- get
                             let (mp',p') = change (mp,p)
                             put (mp',ineq)
                             return p'
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
    solveNext :: EqualityProblem -> StateT (VariableMapping, InequalityProblem) Maybe EqualityProblem
    solveNext [] = return []
    solveNext (e:es) = -- We transform the kth variable into sigma, effectively
                       -- So once we have x_k = ... (in terms of sigma) we add a_k * RHS
                       -- to all other equations, AFTER zeroing the a_k coefficient (so
                       -- that the multiple of sigma is added on properly)
                       modify change >> change' (e:es) >>= liftF normaliseEq
                         where
                           change' p = do (mp,ineq) <- get
                                          let (mp',p') = change (mp,p)
                                          put (mp',ineq)
                                          return p'
                           change = transformPair (addToMapping (k,x_k_eq)) (map alterEquation)
                         
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
solveAndPrune' :: VariableMapping -> EqualityProblem -> InequalityProblem -> Maybe (VariableMapping,InequalityProblem)
solveAndPrune' vm [] ineq = return (vm,ineq)
solveAndPrune' vm eq ineq = solveConstraints vm eq ineq >>= (seqPair . transformPair return pruneAndCheck) >>= (\(x,(y,z)) -> solveAndPrune' x y z)

solveAndPrune :: EqualityProblem -> InequalityProblem -> Maybe (VariableMapping,InequalityProblem)
solveAndPrune eq = solveAndPrune' (defaultMapping $ snd $ bounds $ head eq) eq

-- | Returns the number of variables (of x_1 .. x_n; x_0 is not counted)
-- that have non-zero coefficients in the given inequality problems.
numVariables :: InequalityProblem -> Int
numVariables ineq = length (nub $ concatMap findVars ineq)
  where
    findVars = map fst . filter ((/= 0) . snd) . tail . assocs

-- | Eliminating the inequalities works as follows:
--
-- Rearrange (and normalise) equations for a particular variable x_k to eliminate so that 
-- a_k is always positive and you have:
--  A: a_Ak . x_k <= sum (i is 0 to n, without k) a_Ai . x_i
--  B: a_Bk . x_k >= sum (i is 0 to n, without k) a_Bi . x_i
--  C: equations where a_k is zero.
--
-- Determine if there is an integer solution for x_k:
--
-- TODO
--
-- Form lots of new equations:
--  Given  a_Ak . x_k <= RHS(A)
--         a_Bk . x_k >= RHS(B)
--  We can get (since a_Ak and a_bk are positive):
--         a_Ak . A_Bk . x_k <= A_Bk . RHS(A)
--         a_Ak . A_Bk . x_k >= A_Ak . RHS(B)
--  For every combination of the RHS(A) and RHS(B) generate an inequality: a_Bk . RHS(A) - a_Ak . RHS(B) >=0
-- Add these new equations to the set C, and iterate

fmElimination :: InequalityProblem -> InequalityProblem
fmElimination ineq = fmElimination' (presentItems ineq) (map normaliseIneq ineq)
  where
    -- Finds all variables that have at least one non-zero coefficient in the equation set.
    -- a_0 is ignored; 0 will never be in the returned list
    presentItems :: InequalityProblem -> [Int]
    presentItems = nub . map fst . filter ((/= 0) . snd) . concatMap (tail . assocs)

    fmElimination' :: [Int] -> InequalityProblem -> InequalityProblem
    fmElimination' [] ineq = ineq
    fmElimination' (k:ks) ineq = fmElimination' ks (map normaliseIneq $ eliminate k ineq)
    
    --TODO should we still be checking for redundant equations in the new ones we generate?
    
    eliminate :: Int -> InequalityProblem -> InequalityProblem
    eliminate k ineq = eqC ++ map (uncurry pairIneqs) (product2 (eqA,eqB))
      where
        (eqA,eqB,eqC) = partition ineq
      
        -- We need to partition the related equations into sets A,B and C.
        -- C is straightforward (a_k is zero).
        -- In set B, a_k > 0, and "RHS(B)" (as described above) is the negation of the other
        -- coefficients.  Therefore "-RHS(B)" is the other coefficients as-is.
        -- In set A, a_k < 0,  and "RHS(A)" (as described above) is the other coefficients, untouched
        -- So we simply zero out a_k, and return the rest, associated with the absolute value of a_k.
        partition :: InequalityProblem -> ([(Integer, InequalityConstraintEquation)], [(Integer,InequalityConstraintEquation)], [InequalityConstraintEquation])
        partition = (\(x,y,z) -> (concat x, concat y, concat z)) . unzip3 . map partition'
          where
            partition' e | a_k == 0 = ([],[],[e])
                         | a_k <  0 = ([(abs a_k, e // [(k,0)])],[],[])
                         | a_k >  0 = ([],[(abs a_k, e // [(k,0)])],[])
              where
                a_k = e ! k
        
        pairIneqs :: (Integer, InequalityConstraintEquation) -> (Integer, InequalityConstraintEquation) -> InequalityConstraintEquation
        pairIneqs (x,ex) (y,ey) = arrayZipWith (+) (amap (* y) ex) (amap (* x) ey)

    normaliseIneq :: InequalityConstraintEquation -> InequalityConstraintEquation
    normaliseIneq ineq | g > 1     = arrayMapWithIndex norm ineq
                       | otherwise = ineq
      where
        norm ind val | ind == 0  = normaliseUnits val
                     | otherwise = val `div` g
      
        g = mygcdList $ tail $ elems ineq
        -- I think div would do here, because g will always be positive, but
        -- I feel safer using the mathematical description:
        normaliseUnits a_0 = floor $ (fromInteger a_0 :: Double) / (fromInteger g)
