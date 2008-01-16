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

module ArrayUsageCheck (checkArrayUsage, FlattenedExp(..), makeEquations, VarMap) where

import Control.Monad.Error
import Control.Monad.State
import Data.Array.IArray
import Data.Generics hiding (GT)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import qualified AST as A
import CompState
import Errors
import FlowGraph
import Metadata
import Omega
import Pass
import Types
import Utils

-- TODO we should probably calculate this from the CFG
checkArrayUsage :: Data a => a -> PassM a
checkArrayUsage tree = (mapM_ checkPar $ listify (const True) tree) >> return tree
  where
    -- TODO this doesn't actually check that the uses are in parallel;
    -- they might be in sequence within the parallel!
    checkPar :: A.Process -> PassM ()
    checkPar (A.Par m _ p) = mapM_ (checkIndexes m) $ Map.toList $ Map.fromListWith (++) $ mapMaybe groupArrayIndexes $ listify (const True) p
    checkPar _ = return ()
    
    groupArrayIndexes :: A.Variable -> Maybe (String,[A.Expression])
    -- TODO this is quite hacky:
    groupArrayIndexes (A.SubscriptedVariable _ (A.Subscript _ e) (A.Variable _ n))
      = Just (A.nameName n, [e])
    groupArrayIndexes _ = Nothing
    
    checkIndexes :: Meta -> (String,[A.Expression]) -> PassM ()
    checkIndexes m (arrName, indexes)
      = do userArrName <- getRealName (A.Name undefined undefined arrName)
           arrType <- typeOfName (A.Name undefined undefined arrName)
           (arrLength,checkable) <- case arrType of
             A.Array (A.Dimension d:_) _ -> return (d,True)
             A.Array (A.UnknownDimension:_) _ -> return (undefined, False)
             _ -> dieP m $ "Cannot usage check array \"" ++ userArrName ++ "\"; found to be of type: " ++ show arrType
           if not checkable
             then return ()
             else case makeEquations indexes (makeConstant emptyMeta arrLength) of
               Left err -> dieP m $ "Could not work with array indexes for array \"" ++ userArrName ++ "\": " ++ err
               Right [] -> return () -- No problems to work with
               Right problems ->
                 case mapMaybe (\(vm,p) -> seqPair (return vm,uncurry solveProblem p)) problems of
                   -- No solutions; no worries!
                   [] -> return ()
                   ((varMapping,vm):_) -> do sol <- formatSolution varMapping (getCounterEqs vm)
                                             dieP m $ "Overlapping indexes of array \"" ++ userArrName ++ "\" when: " ++ sol
    
    formatSolution :: VarMap -> Map.Map CoeffIndex Integer -> PassM String
    formatSolution varToIndex indexToConst = do names <- mapM valOfVar $ Map.assocs varToIndex
                                                return $ concat $ intersperse " , " $ catMaybes names
      where
        valOfVar (varExp,k) = case Map.lookup k indexToConst of 
                                 Nothing -> return Nothing
                                 Just val -> do varExp' <- showFlattenedExp varExp
                                                return $ Just $ varExp' ++ " = " ++ show val

    -- TODO this is surely defined elsewhere already?
    getRealName :: A.Name -> PassM String
    getRealName n = lookupName n >>* A.ndOrigName
    
    showFlattenedExp :: FlattenedExp -> PassM String
    showFlattenedExp (Const n) = return $ show n
    showFlattenedExp (Scale n ((A.Variable _ vn),vi))
      = do vn' <- getRealName vn >>* (\s -> if vi == 0 then s else s ++ replicate vi '\'' )
           case n of
             1  -> return vn'
             -1 -> return $ "-" ++ vn'
             _  -> return $ (show n) ++ "*" ++ vn'
    showFlattenedExp (Modulo top bottom)
      = do top' <- showFlattenedExpSet top
           bottom' <- showFlattenedExpSet bottom
           case onlyConst (Set.toList bottom) of
             Just _  -> return $ "(" ++ top' ++ " / " ++ bottom' ++ ")"
             Nothing -> return $ "((" ++ top' ++ " REM " ++ bottom' ++ ") - " ++ top' ++ ")"
    showFlattenedExp (Divide top bottom)
      = do top' <- showFlattenedExpSet top
           bottom' <- showFlattenedExpSet bottom
           return $ "(" ++ top' ++ " / " ++ bottom' ++ ")"
    
    showFlattenedExpSet :: Set.Set FlattenedExp -> PassM String
    showFlattenedExpSet s = liftM concat $ sequence $ intersperse (return " + ") $ map showFlattenedExp $ Set.toList s

-- | A type for inside makeEquations:
data FlattenedExp
  = Const Integer 
  | Scale Integer (A.Variable, Int)
  | Modulo (Set.Set FlattenedExp) (Set.Set FlattenedExp)
  | Divide (Set.Set FlattenedExp) (Set.Set FlattenedExp)

instance Eq FlattenedExp where
  a == b = EQ == compare a b

instance Ord FlattenedExp where
  compare (Const _) (Const _) = EQ
  compare (Const _) _ = LT
  compare _ (Const _) = GT
  compare (Scale _ (lv,li)) (Scale _ (rv,ri)) = combineCompare [customVarCompare lv rv, compare li ri]
  compare (Scale {}) _ = LT
  compare _ (Scale {}) = GT
  compare (Modulo ltop lbottom) (Modulo rtop rbottom)
    = combineCompare [compare ltop rtop, compare lbottom rbottom]
  compare (Modulo {}) _ = LT
  compare _ (Modulo {}) = GT
  compare (Divide ltop lbottom) (Divide rtop rbottom)
    = combineCompare [compare ltop rtop, compare lbottom rbottom]

customVarCompare :: A.Variable -> A.Variable -> Ordering
customVarCompare (A.Variable _ (A.Name _ _ lname)) (A.Variable _ (A.Name _ _ rname)) = compare lname rname
-- TODO the rest

onlyConst :: [FlattenedExp] -> Maybe Integer
onlyConst [] = Just 0
onlyConst ((Const n):es) = liftM2 (+) (return n) $ onlyConst es
onlyConst _ = Nothing


makeExpSet :: [FlattenedExp] -> Either String (Set.Set FlattenedExp)
makeExpSet = foldM makeExpSet' Set.empty
  where
    makeExpSet' :: Set.Set FlattenedExp -> FlattenedExp -> Either String (Set.Set FlattenedExp)
    makeExpSet' accum (Const n) = return $ insert (addConst n) (Const n) accum
    makeExpSet' accum (Scale n v) = return $ insert (addScale n v) (Scale n v) accum
    makeExpSet' accum m@(Modulo {}) | Set.member m accum = throwError "Cannot have repeated REM items in an expression"
                                    | otherwise = return $ Set.insert m accum
    makeExpSet' accum d@(Divide {}) | Set.member d accum = throwError "Cannot have repeated (/) items in an expression"
                                    | otherwise = return $ Set.insert d accum
    
    insert :: (FlattenedExp -> Set.Set FlattenedExp -> Maybe (Set.Set FlattenedExp)) -> FlattenedExp -> Set.Set FlattenedExp -> Set.Set FlattenedExp
    insert f e s = case Set.fold insert' (Set.empty,False) s of
                     (s',True) -> s'
                     _ -> Set.insert e s
      where
        insert' :: FlattenedExp -> (Set.Set FlattenedExp, Bool) -> (Set.Set FlattenedExp, Bool)
        insert' e (s,b) = case f e s of
                            Just s' -> (s', True)
                            Nothing -> (Set.insert e s, False)
    
    addConst :: Integer -> FlattenedExp -> Set.Set FlattenedExp -> Maybe (Set.Set FlattenedExp)
    addConst x (Const n) s = Just $ Set.insert (Const (n + x)) s
    addConst _ _ _ = Nothing

    addScale :: Integer -> (A.Variable,Int) -> FlattenedExp -> Set.Set FlattenedExp -> Maybe (Set.Set FlattenedExp)
    addScale x (lv,li) (Scale n (rv,ri)) s
      | (EQ == customVarCompare lv rv) && (li == ri) = Just $ Set.insert (Scale (x + n) (rv,ri)) s
      | otherwise = Nothing
    addScale _ _ _ _ = Nothing

type VarMap = Map.Map FlattenedExp Int

-- | Given a list of expressions, an expression representing the upper array bound, returns either an error
-- (because the expressions can't be handled, typically) or a set of equalities, inequalities and mapping from
-- (unique, munged) variable name to variable-index in the equations.
-- TODO probably want to take this into the PassM monad at some point, to use the Meta in the error message
makeEquations :: [A.Expression] -> A.Expression -> Either String [(VarMap, (EqualityProblem, InequalityProblem))]
makeEquations es high = makeEquations' >>* (\(s,v,lh) -> [(s,squareEquations eqIneq) | eqIneq <- pairEqsAndBounds v lh])
  where
  
    -- | The body of makeEquations; returns the variable mapping, the list of (nx,ex) pairs and a pair
    -- representing the upper and lower bounds of the array (inclusive).    
    makeEquations' :: Either String (VarMap, [[(EqualityConstraintEquation,EqualityProblem,InequalityProblem)]], (EqualityConstraintEquation, EqualityConstraintEquation))
    makeEquations' = do ((v,h),s) <- (flip runStateT) Map.empty $
                           do flattened <- lift (mapM flatten es)
                              eqs <- mapM makeEquation flattened
                              high' <- (lift $ flatten high) >>= makeEquation 
                              high'' <- case high' of
                                          [(h,_,_)] -> return h
                                          _ -> throwError "Multiple possible upper bounds not supported"
                              return (eqs,high'')
                        return (s,v,(amap (const 0) h, addConstant (-1) h))
                              
    -- Note that in all these functions, the divisor should always be positive!
  
    -- Takes an expression, and transforms it into an expression like:
    -- (e_0 + e_1 + e_2) / d
    -- where d is a constant (non-zero!) integer, and each e_k
    -- is either a const, a var, const * var, or (const * var) % const [TODO].
    -- If the expression cannot be transformed into such a format, an error is returned
    flatten :: A.Expression -> Either String [FlattenedExp]
    flatten (A.Literal _ _ (A.IntLiteral _ n)) = return [Const (read n)]
    flatten (A.Dyadic m op lhs rhs) | op == A.Add   = combine' (flatten lhs) (flatten rhs)
                                    | op == A.Subtr = combine' (flatten lhs) (liftM (scale (-1)) $ flatten rhs)
                                    | op == A.Mul   = multiplyOut' (flatten lhs) (flatten rhs)
                                    | op == A.Rem   = liftM2L Modulo (flatten lhs) (flatten rhs)
                                    | op == A.Div   = liftM2L Divide (flatten lhs) (flatten rhs)
                                    | otherwise     = throwError ("Unhandleable operator found in expression: " ++ show op)
    flatten (A.ExprVariable _ v) = return [Scale 1 (v,0)]
    flatten other = throwError ("Unhandleable item found in expression: " ++ show other)

--    liftM2L :: (Ord a, Ord b, Monad m) => (Set.Set a -> Set.Set b -> c) -> m [a] -> m [b] -> m [c]
    liftM2L f x y = liftM (:[]) $ liftM2 f (x >>= makeExpSet) (y >>= makeExpSet)

    --TODO we need to handle lots more different expression types in future.
    
    multiplyOut' :: Either String [FlattenedExp] -> Either String [FlattenedExp] -> Either String [FlattenedExp]
    multiplyOut' x y = do {x' <- x; y' <- y; multiplyOut x' y'}
    
    multiplyOut :: [FlattenedExp] -> [FlattenedExp] -> Either String [FlattenedExp]
    multiplyOut lhs rhs = mapM (uncurry mult) pairs 
      where
        pairs = product2 (lhs,rhs)

        mult :: FlattenedExp -> FlattenedExp -> Either String FlattenedExp
        mult (Const x) (Const y) = return $ Const (x*y)
        mult (Scale n v) (Const x) = return $ Scale (n*x) v
        mult (Const x) (Scale n v) = return $ Scale (n*x) v
        mult (Scale _ v) (Scale _ v')
          = throwError $ "Cannot deal with non-linear equations; during flattening found: "
              ++ show v ++ " * " ++ show v'
    
    -- | Scales a flattened expression by the given integer scaling.
    scale :: Integer -> [FlattenedExp] -> [FlattenedExp]
    scale sc = map scale'
      where
        scale' (Const n) = Const (n * sc)
        scale' (Scale n v) = Scale (n * sc) v

    -- | An easy way of applying combine to two monadic returns
    combine' :: Either String [FlattenedExp] -> Either String [FlattenedExp] -> Either String [FlattenedExp]
    combine' = liftM2 combine
    
    -- | Combines (adds) two flattened expressions.
    combine :: [FlattenedExp] -> [FlattenedExp] -> [FlattenedExp]
    combine = (++)
 
  
    -- | Finds the index associated with a particular variable; either by finding an existing index
    -- or allocating a new one.
    varIndex :: FlattenedExp -> StateT (VarMap) (Either String) Int
    varIndex (Scale _ (var@(A.Variable _ (A.Name _ _ varName)),vi))
      = do st <- get
           let (st',ind) = case Map.lookup (Scale 1 (var,vi)) st of
                             Just val -> (st,val)
                             Nothing -> let newId = (1 + (maximum $ 0 : Map.elems st)) in
                                        (Map.insert (Scale 1 (var,vi)) newId st, newId)
           put st'
           return ind
    varIndex mod@(Modulo top bottom)
      = do st <- get
           let (st',ind) = case Map.lookup mod st of
                             Just val -> (st,val)
                             Nothing -> let newId = (1 + (maximum $ 0 : Map.elems st)) in
                                        (Map.insert mod newId st, newId)
           put st'
           return ind           

    -- | Pairs all possible combinations of the list of equations.
    pairEqsAndBounds :: [[(EqualityConstraintEquation, EqualityProblem, InequalityProblem)]] -> (EqualityConstraintEquation, EqualityConstraintEquation) -> [(EqualityProblem, InequalityProblem)]
    pairEqsAndBounds items bounds = (concatMap (uncurry pairEqs) . allPairs) items 
      where
        pairEqs :: [(EqualityConstraintEquation, EqualityProblem, InequalityProblem)]
          -> [(EqualityConstraintEquation, EqualityProblem, InequalityProblem)]
          -> [(EqualityProblem, InequalityProblem)]
        pairEqs p0 p1 = map (uncurry pairEqs') $ product2 (p0,p1)
      
        pairEqs' :: (EqualityConstraintEquation, EqualityProblem, InequalityProblem)
          -> (EqualityConstraintEquation, EqualityProblem, InequalityProblem)
          -> (EqualityProblem, InequalityProblem)
        pairEqs' (ex,eqX,ineqX) (ey,eqY,ineqY) = ([arrayZipWith' 0 (-) ex ey] ++ eqX ++ eqY, ineqX ++ ineqY ++ getIneqs bounds [ex,ey])
    
    -- | Given a (low,high) bound (typically: array dimensions), and a list of equations ex,
    -- forms the possible inequalities: 
    -- * ex >= low
    -- * ex <= high
    getIneqs :: (EqualityConstraintEquation, EqualityConstraintEquation) -> [EqualityConstraintEquation] -> [InequalityConstraintEquation]
    getIneqs (low, high) = concatMap getLH
      where
        -- eq >= low => eq - low >= 0
        -- eq <= high => high - eq >= 0
      
        getLH :: EqualityConstraintEquation -> [InequalityConstraintEquation]
        getLH eq = [eq `addEq` (amap negate low),high `addEq` amap negate eq]
        
        addEq = arrayZipWith' 0 (+)
    
    -- | Given an expression, forms equations (and accompanying additional equation-sets) and returns it
    makeEquation :: [FlattenedExp] -> StateT (VarMap) (Either String) [(EqualityConstraintEquation, EqualityProblem, InequalityProblem)]
    makeEquation summedItems
      = do eqs <- process summedItems
           return $ map (transformTriple mapToArray (map mapToArray) (map mapToArray)) eqs
      where
        process = foldM makeEquation' empty
      
        makeEquation' :: [(Map.Map Int Integer,[Map.Map Int Integer], [Map.Map Int Integer])] -> FlattenedExp -> StateT (VarMap) (Either String) [(Map.Map Int Integer,[Map.Map Int Integer], [Map.Map Int Integer])]
        makeEquation' m (Const n) = return $ add (0,n) m
        makeEquation' m sc@(Scale n v) = varIndex sc >>* (\ind -> add (ind, n) m)
        makeEquation' m mod@(Modulo top bottom)
          = do top' <- process $ Set.toList top
               top'' <- case top' of
                          [(t,_,_)] -> return t
                          _ -> throwError "Modulo or divide not allowed in the numerator of Modulo"
               bottom' <- process $ Set.toList bottom
               topIndex <- varIndex mod
               case onlyConst (Set.toList bottom) of
                 Just bottomConst -> 
                   let add_x_plus_my = zipMap plus top'' . zipMap plus (Map.fromList [(topIndex,bottomConst)]) in
                   return $
                     -- The zero option (x = 0, x REM y = 0):
                   ( map (transformTriple id (++ [top'']) id) m)
                   ++
                     -- The top-is-positive option:
                   ( map (transformTriple add_x_plus_my id (++
                      -- x >= 1
                      [zipMap plus (Map.fromList [(0,-1)]) top''
                      -- m <= 0
                      ,Map.fromList [(topIndex,-1)]
                      -- x + my + 1 - |y| <= 0
                      ,Map.map negate $ add_x_plus_my $ Map.fromList [(0,1 - bottomConst)]
                      -- x + my >= 0
                      ,add_x_plus_my $ Map.empty])
                     ) m) ++
                    -- The top-is-negative option:
                   ( map (transformTriple add_x_plus_my id (++
                      -- x <= -1
                      [add' (0,-1) $ Map.map negate top''
                      -- m >= 0
                      ,Map.fromList [(topIndex,1)]
                      -- x + my - 1 + |y| >= 0
                      ,add_x_plus_my $ Map.fromList [(0,bottomConst - 1)]
                      -- x + my <= 0
                      ,Map.map negate $ add_x_plus_my Map.empty])
                     ) m)
                 _ ->
                   do bottom'' <- case bottom' of
                                    [(b,_,_)] -> return b
                                    _ -> throwError "Modulo or divide not allowed in the divisor of Modulo"
                      return $
                        -- The zero option (x = 0, x REM y = 0):
                        (map (transformTriple id (++ [top'']) id) m)
                        -- The rest:
                        ++ twinItems True True (top'', topIndex) bottom''
                        ++ twinItems True False (top'', topIndex) bottom''
                        ++ twinItems False True (top'', topIndex) bottom''
                        ++ twinItems False False (top'', topIndex) bottom''
          where
            -- Each pair for modulo (variable divisor) depending on signs of x and y (in x REM y):
            twinItems :: Bool -> Bool -> (Map.Map Int Integer,Int) -> Map.Map Int Integer ->
              [(Map.Map Int Integer,[Map.Map Int Integer], [Map.Map Int Integer])]
            twinItems xPos yPos (top,topIndex) bottom
              = (map (transformTriple (zipMap plus top) id
                  (++ [xEquation]
                   ++ [xLowerBound False]
                   ++ [xUpperBound False])) m)
                ++ (map (transformTriple (zipMap plus top . add' (topIndex,1)) id
                  (++ [xEquation]
                   ++ [xLowerBound True]
                   ++ [xUpperBound True]
                   -- We want to add the bounds for a and y as follows:
                   -- xPos yPos | Equation
                   -- T    T    | -y - a  >= 0
                   -- T    F    | y - a >= 0
                   -- F    T    | a - y  >= 0
                   -- F    F    | a + y  >= 0
                   -- Therefore the sign of a is (not xPos), the sign of y is (not yPos)
                   ++ [add' (topIndex,if xPos then -1 else 1) (signEq (not yPos) bottom)])) m)
              where
                -- x >= 1 or x <= -1  (rearranged: -1 + x >= 0 or -1 - x >= 0)
                xEquation = add' (0,-1) (signEq xPos top)
                -- We include (x [+ a] >= 0 or x [+ a] <= 0) even though they are redundant in some cases (addA = False):
                xLowerBound addA = signEq xPos $ (if addA then add' (topIndex,1) else id) top
                -- We want to add the bounds as follows:
                -- xPos yPos | Equation
                -- T    T    | y - 1 - x - a  >= 0
                -- T    F    | -y - 1 - x - a >= 0
                -- F    T    | x + a - 1 + y  >= 0
                -- F    F    | x + a - y - 1  >= 0
                -- Therefore the sign of y in the equation is yPos, the sign of x and a is (not xPos)
                xUpperBound addA = add' (0,-1) $ zipMap plus (signEq (not xPos) ((if addA then add' (topIndex,1) else id) top)) (signEq yPos bottom)
                
                signEq sign eq = if sign then eq else Map.map negate eq
            
        makeEquation' m (Divide top bottom) = throwError "TODO Divide"
        
        empty :: [(Map.Map Int Integer,[Map.Map Int Integer], [Map.Map Int Integer])]
        empty = [(Map.empty,[],[])]
        
        plus :: Num n => Maybe n -> Maybe n -> Maybe n
        plus x y = Just $ (fromMaybe 0 x) + (fromMaybe 0 y)
        
        add' :: (Int,Integer) -> Map.Map Int Integer -> Map.Map Int Integer
        add' (m,n) = Map.insertWith (+) m n
        
        add :: (Int,Integer) -> [(Map.Map Int Integer,a,b)] -> [(Map.Map Int Integer,a,b)]
        add (m,n) = map $ transformTriple (Map.insertWith (+) m n) id id
    
    -- | Converts a map to an array.  Any missing elements in the middle of the bounds are given the value zero.
    -- Could probably be moved to Utils
    mapToArray :: (IArray a v, Num v, Num k, Ord k, Ix k) => Map.Map k v -> a k v
    mapToArray m = accumArray (+) 0 (0, highest') . Map.assocs $ m
      where
        highest' = maximum $ 0 : Map.keys m
    
    -- | Given a pair of equation sets, makes all the equations in the lists be the length
    -- of the longest equation.  All missing elements are of course given value zero.
    squareEquations :: ([Array CoeffIndex Integer],[Array CoeffIndex Integer]) -> ([Array CoeffIndex Integer],[Array CoeffIndex Integer])
    squareEquations (eqs,ineqs) = uncurry transformPair (mkPair $ map $ makeSize (0,highest) 0) (eqs,ineqs)
    
      where
        makeSize :: (Show i, Show e,IArray a e, Ix i, Enum i) => (i,i) -> e -> a i e -> a i e
        makeSize size def arr = array size [(i,arrayLookupWithDefault def arr i) | i <- [fst size .. snd size]]
      
        highest = maximum $ 0 : (concatMap indices $ eqs ++ ineqs)

