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

module ArrayUsageCheck (checkArrayUsage, FlattenedExp(..), makeEquations, makeReplicatedEquations, usageCheckPass, VarMap) where

import Control.Monad.Error
import Control.Monad.State
import Data.Array.IArray
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
import UsageCheck
import Utils

usageCheckPass :: Pass
usageCheckPass t = do g' <- buildFlowGraph labelFunctions t
                      g <- case g' of
                        Left err -> die err
                        Right g -> return g
                      checkArrayUsage g
                      return t


-- TODO we should probably calculate this from the CFG
checkArrayUsage :: forall m. (Die m, CSM m) => FlowGraph m (Maybe Decl, Vars) -> m ()
checkArrayUsage graph = sequence_ $ checkPar checkArrayUsage' graph
  where
    -- TODO take proper account of replication!
    flatten :: ParItems a -> [a]
    flatten (ParItem x) = [x]
    flatten (ParItems xs) = concatMap flatten xs
    flatten (RepParItem _ x) = flatten x --TODO

    checkArrayUsage' :: (Meta, ParItems (Maybe Decl, Vars)) -> m ()
    checkArrayUsage' (m,p) = mapM_ (checkIndexes m) $ Map.toList $ 
      foldl (Map.unionWith (\(a,b) (c,d) -> (a ++ c, b ++ d))) Map.empty $ map (groupArrayIndexes . snd) $ flatten p
    
    -- Returns (array name, list of written-to indexes, list of read-from indexes)
    groupArrayIndexes :: Vars -> Map.Map String ([A.Expression], [A.Expression])
    groupArrayIndexes vs = zipMap join (makeList (writtenVars vs)) (makeList (readVars vs))
      where
        join :: Maybe [a] -> Maybe [a] -> Maybe ([a],[a])
        join x y = Just (maybe [] id x, maybe [] id y)
      
        makeList :: Set.Set Var -> Map.Map String [A.Expression]
        makeList = Set.fold (maybe id (uncurry $ Map.insertWith (++)) . getArrayIndex) Map.empty
      
--        sortAndGroupBy :: (a -> a -> Ordering) -> [a] -> [[a]]
--        sortAndGroupBy f = groupBy ((== EQ) . f) . sortBy f
      
        -- TODO this is quite hacky:
        getArrayIndex :: Var -> Maybe (String, [A.Expression])
        getArrayIndex (Var (A.SubscriptedVariable _ (A.Subscript _ e) (A.Variable _ n)))
          = Just (A.nameName n, [e])
        getArrayIndex _ = Nothing
    
    checkIndexes :: Meta -> (String,([A.Expression],[A.Expression])) -> m ()
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
    
    formatSolution :: VarMap -> Map.Map CoeffIndex Integer -> m String
    formatSolution varToIndex indexToConst = do names <- mapM valOfVar $ Map.assocs varToIndex
                                                return $ concat $ intersperse " , " $ catMaybes names
      where
        valOfVar (varExp,k) = case Map.lookup k indexToConst of 
                                 Nothing -> return Nothing
                                 Just val -> do varExp' <- showFlattenedExp varExp
                                                return $ Just $ varExp' ++ " = " ++ show val

    -- TODO this is surely defined elsewhere already?
    getRealName :: A.Name -> m String
    getRealName n = lookupName n >>* A.ndOrigName
    
    showFlattenedExp :: FlattenedExp -> m String
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
    
    showFlattenedExpSet :: Set.Set FlattenedExp -> m String
    showFlattenedExpSet s = liftM concat $ sequence $ intersperse (return " + ") $ map showFlattenedExp $ Set.toList s

-- | A type for inside makeEquations:
data FlattenedExp
  = Const Integer 
  | Scale Integer (A.Variable, Int)
  | Modulo (Set.Set FlattenedExp) (Set.Set FlattenedExp)
  | Divide (Set.Set FlattenedExp) (Set.Set FlattenedExp)

--TODO change the A.Variable to Var, and automatically derive Eq and Ord

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

onlyConst :: [FlattenedExp] -> Maybe Integer
onlyConst [] = Just 0
onlyConst ((Const n):es) = liftM2 (+) (return n) $ onlyConst es
onlyConst _ = Nothing

-- | A data type representing an array access.  Each triple is (index, extra-equalities, extra-inequalities).
-- A Single item can be paired with every other access.
-- Each item of a Group cannot be paired with each other, but can be paired with each other access.
-- With a Replicated, each item in the left branch can be paired with each item in the right branch.
-- Each item in the left branch can be paired with each other, and each item in the left branch can
-- be paired with all other items.
data ArrayAccess =
  Single (ArrayAccessType, (EqualityConstraintEquation, EqualityProblem, InequalityProblem))
  | Group [(ArrayAccessType, (EqualityConstraintEquation, EqualityProblem, InequalityProblem))]
  | Replicated [ArrayAccess] [ArrayAccess]

data ArrayAccessType = AAWrite | AARead

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

-- | Given a list of (replicated variable, start, count), a list of (written,read) parallel array accesses,
-- the length of the array, returns the problems.
--
-- The general strategy is as follows.
-- For every array index (here termed an "access"), we transform it into
-- the usual [FlattenedExp] using the flatten function.  Then we also transform
-- any access that features a replicated variable into its mirrored version
-- where each i is changed into i'.  This is done by using vi=(variable "i",0)
-- (in Scale _ vi) for the plain (normal) version, and vi=(variable "i",1)
-- for the prime (mirror) version.
--
-- Then the equations have bounds added.  The rules are fairly simple; if
-- any of the transformed EqualityConstraintEquation representing an access
-- have a non-zero i (and/or i'), the bound for that variable is added.
-- So for example, an expression like "i = i' + 3" would have the bounds for
-- both i and i' added (which would be near-identical, e.g. 1 <= i <= 6 and
-- 1 <= i' <= 6).
--
-- The remainder of the work (correctly pairing equations) is done by
-- squareAndPair.
makeReplicatedEquations :: [(A.Variable, A.Expression, A.Expression)] -> ([A.Expression],[A.Expression]) -> A.Expression ->
  Either String [(VarMap, (EqualityProblem, InequalityProblem))]
makeReplicatedEquations repVars accesses bound
  = do flattenedAccesses <- applyPairM (mapM flatten) accesses
       let flattenedAccessesMirror = applyPair concat $ unzip $ map (\(v,_,_) -> applyPair (map (setIndexVar v 1)) flattenedAccesses) repVars
       bound' <- flatten bound
       ((v,h,repVars',repVarIndexes),s) <- (flip runStateT) Map.empty $
          do repVars' <- mapM (\(v,s,c) ->
               do s' <- lift (flatten s) >>= makeEquation (error "Type is irrelevant for replication count")
                     >>= getSingleAccessItem "Modulo or Divide not allowed in replication start"
                  c' <- lift (flatten c) >>= makeEquation (error "Type is irrelevant for replication count")
                     >>= getSingleAccessItem "Modulo or Divide not allowed in replication count"
                  return (v,s',c')) repVars
             accesses' <- mapM (makeEquationWithPossibleRepBounds repVars') =<< makeEquationsWR flattenedAccesses
             accesses'' <- mapM (makeEquationWithPossibleRepBounds repVars') =<< makeEquationsWR flattenedAccessesMirror
             high <- makeEquation (error "Type is irrelevant for uppper bound") bound'
               >>= getSingleAccessItem "Multiple possible upper bounds not supported"
             repVarIndexes <- mapM (\(v,_,_) -> seqPair (varIndex (Scale 1 (v,0)), varIndex (Scale 1 (v,1)))) repVars
             return (Replicated accesses' accesses'',high, repVars',repVarIndexes)
       return $ squareAndPair repVarIndexes s [v] (amap (const 0) h, addConstant (-1) h)

  where
    makeEquationsWR :: ([[FlattenedExp]],[[FlattenedExp]]) -> StateT (VarMap) (Either String) [ArrayAccess]
    makeEquationsWR (w,r) = do w' <- mapM (makeEquation AAWrite) w
                               r' <- mapM (makeEquation AARead) r
                               return (w' ++ r')
    
  
    setIndexVar :: A.Variable -> Int -> [FlattenedExp] -> [FlattenedExp]
    setIndexVar tv ti es = case mapAccumL (setIndexVar' tv ti) False es of
      (_, es') -> es'
  
    setIndexVar' :: A.Variable -> Int -> Bool -> FlattenedExp -> (Bool,FlattenedExp)
    setIndexVar' tv ti b s@(Scale n (v,_))
      | EQ == customVarCompare tv v = (True,Scale n (v,ti))
      | otherwise = (b,s)
    setIndexVar' _ _ b e = (b,e)

    makeEquationWithPossibleRepBounds :: [(A.Variable, EqualityConstraintEquation, EqualityConstraintEquation)] -> 
      ArrayAccess -> StateT (VarMap) (Either String) ArrayAccess
    makeEquationWithPossibleRepBounds [] item = return item
    makeEquationWithPossibleRepBounds ((v,lower,upper):vars) item
           -- We fold over the variables, altering the items one at a time via mapM:
      = do item' <- makeEquationWithPossibleRepBounds vars item
           flip addPossibleRepBound' (v,0,lower,upper) item' >>=
             flip addPossibleRepBound' (v,1,lower,upper) 

    addPossibleRepBound' :: ArrayAccess ->
      (A.Variable, Int, EqualityConstraintEquation, EqualityConstraintEquation) ->
      StateT (VarMap) (Either String) ArrayAccess
    addPossibleRepBound' (Group accesses) v = mapM (seqPair . transformPair return (flip addPossibleRepBound v)) accesses >>* Group
    addPossibleRepBound' (Replicated acc0 acc1) v
      = do acc0' <- mapM (flip addPossibleRepBound' v) acc0
           acc1' <- mapM (flip addPossibleRepBound' v) acc1
           return $ Replicated acc0' acc1'
    addPossibleRepBound' (Single (t,acc)) v = addPossibleRepBound acc v >>* (\x -> Single (t,x))

    addPossibleRepBound :: (EqualityConstraintEquation, EqualityProblem, InequalityProblem) ->
      (A.Variable, Int, EqualityConstraintEquation, EqualityConstraintEquation) ->
      StateT (VarMap) (Either String) (EqualityConstraintEquation, EqualityProblem, InequalityProblem)
    addPossibleRepBound (item,eq,ineq) (var,index,lower,upper)
      = do index <- varIndex (Scale 1 vi)
           let boundEqs = if arrayLookupWithDefault 0 item index /= 0
                            then [add (index,1) $ amap negate lower,add (index,-1) upper]
                            else []
           return (item,eq,ineq ++ boundEqs)
      where
        vi = (var,index)
      
        add :: (Int,Integer) -> Array Int Integer -> Array Int Integer
        add (ind,val) a = (makeSize (newMin, newMax) 0 a) // [(ind, (arrayLookupWithDefault 0 a ind) + val)]
          where
            newMin = minimum [fst $ bounds a, ind]
            newMax = maximum [snd $ bounds a, ind]        
            
-- Note that in all these functions, the divisor should always be positive!
  
-- Takes an expression, and transforms it into an expression like:
-- (e_0 + e_1 + e_2) / d
-- where d is a constant (non-zero!) integer, and each e_k
-- is either a const, a var, const * var, or (const * var) % const [TODO].
-- If the expression cannot be transformed into such a format, an error is returned
flatten :: A.Expression -> Either String [FlattenedExp]
flatten (A.Literal _ _ (A.IntLiteral _ n)) = return [Const (read n)]
flatten (A.ExprVariable _ v) = return [Scale 1 (v,0)]
flatten (A.Dyadic m op lhs rhs) | op == A.Add   = combine' (flatten lhs) (flatten rhs)
                                | op == A.Subtr = combine' (flatten lhs) (liftM (scale (-1)) $ flatten rhs)
                                | op == A.Mul   = multiplyOut' (flatten lhs) (flatten rhs)
                                | op == A.Rem   = liftM2L Modulo (flatten lhs) (flatten rhs)
                                | op == A.Div   = liftM2L Divide (flatten lhs) (flatten rhs)
                                | otherwise     = throwError ("Unhandleable operator found in expression: " ++ show op)
  where
--    liftM2L :: (Ord a, Ord b, Monad m) => (Set.Set a -> Set.Set b -> c) -> m [a] -> m [b] -> m [c]
    liftM2L f x y = liftM singleton $ liftM2 f (x >>= makeExpSet) (y >>= makeExpSet)

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
        -- TODO test and handle modulo and divide here
    
    -- | Scales a flattened expression by the given integer scaling.
    scale :: Integer -> [FlattenedExp] -> [FlattenedExp]
    scale sc = map scale'
      where
        scale' (Const n) = Const (n * sc)
        scale' (Scale n v) = Scale (n * sc) v
        -- TODO test the other cases then write them

    -- | An easy way of applying combine to two monadic returns
    combine' :: Either String [FlattenedExp] -> Either String [FlattenedExp] -> Either String [FlattenedExp]
    combine' = liftM2 combine
    
    -- | Combines (adds) two flattened expressions.
    combine :: [FlattenedExp] -> [FlattenedExp] -> [FlattenedExp]
    combine = (++)
flatten other = throwError ("Unhandleable item found in expression: " ++ show other)

-- | The "square" refers to making all equations the length of the longest
-- one, and the pair refers to pairing each in a list of array accesses (e.g. 
-- [0, 5, i + 2]) into all possible pairings ([0 == 5, 0 == i + 2, 5 == i + 2])
--
-- There are two complications to this function.
-- 
-- Firstly, the array accesses are not actually given in a plain list, but 
-- instead a list of lists.  This is because for things like modulo, there are
-- groups of possible accesses that should not be paired against each other.
-- For example, you may have something like [0,x,-x] as the three possible
-- options for a modulo.  You want to pair the accesses against other accesses
-- (e.g. y + 6), but not against each other.  So the arguments are passed in
-- in groups: [[0,x,-x],[y + 6]] and groups are paired against each other,
-- but not against themselves.  This all refers to the third argument to the
-- function.  Each item is actually a triple of (item, equalities, inequalities)
-- because the modulo aspect adds additional constraints.
--
-- The other complication comes from replicated variables.
-- The first argument is a list of (plain,prime) coefficient indexes
-- that effectively labels the indexes related to replicated variables.
-- squareAndPair does two things with this information:
--   1. It discards all equations that feature only the prime version of
--      a variable.  You might have passed in the accesses as [[i],[i'],[3]].
--      (Altering the grouping would not be able to solve this particular problem)
--      The pairings generated would be [i == i', i == 3, i' == 3].  But the
--      last two are in effect identical.  Therefore we drop the i' prime
--      version, because it has i' but not i.  In contrast, the first item
--      (i == i') is retained because it features both i and i'.
--   2. For every equation that features both i and i', it adds
--      the inequality "i <= i' - 1".  Because all possible combinations of
--      accesses are examined, in the case of [i,i + 1,i', i' + 1], the pairing
--      will produce both "i = i' + 1" and "i + 1 = i'" so there is no need
--      to vary the inequality itself.
squareAndPair ::
  [(CoeffIndex, CoeffIndex)] ->
  VarMap ->
  [ArrayAccess] ->
  (EqualityConstraintEquation, EqualityConstraintEquation) ->
  [(VarMap, (EqualityProblem, InequalityProblem))] 
squareAndPair repVars s v lh
  = [(s,squareEquations (eq,ineq ++ concat (applyAll (eq,ineq) (map addExtra repVars))))
    | (eq,ineq) <- pairEqsAndBounds v lh
      ,and (map (primeImpliesPlain (eq,ineq)) repVars)
    ]
  where
    itemPresent :: CoeffIndex -> [Array CoeffIndex Integer] -> Bool
    itemPresent x = any (\a -> arrayLookupWithDefault 0 a x /= 0)
    
    primeImpliesPlain :: (EqualityProblem,InequalityProblem) -> (CoeffIndex,CoeffIndex) -> Bool
    primeImpliesPlain (eq,ineq) (plain,prime) =
      if itemPresent prime (eq ++ ineq)
        -- There are primes, check all the plains are present:
        then itemPresent plain (eq ++ ineq)
        -- No prime, therefore fine:
        else True
    
    addExtra :: (CoeffIndex, CoeffIndex) -> (EqualityProblem,InequalityProblem) -> InequalityProblem
    addExtra (plain,prime) (eq, ineq)
      | itemPresent plain (eq ++ ineq) && itemPresent prime (eq ++ ineq) = extraIneq
      | otherwise = []
      where
        extraIneq :: InequalityProblem
          -- prime >= plain + 1  (prime - plain - 1 >= 0)
        extraIneq = [simpleArray [(prime,1), (plain,-1), (0, -1)]]

{-
getSingles :: String -> [ArrayAccess] -> Either String [(EqualityConstraintEquation, EqualityProblem, InequalityProblem)]
getSingles err = mapM getSingle
  where
    getSingle (Single acc) = return acc
    getSingle _ = throwError err
-}

getSingleAccessItem :: MonadTrans m => String -> ArrayAccess -> m (Either String) EqualityConstraintEquation
getSingleAccessItem _ (Single (_,(acc,_,_))) = lift $ return acc
getSingleAccessItem err _ = lift $ throwError err

{-
getSingleAccess :: MonadTrans m => String -> ArrayAccess -> m (Either String) (EqualityConstraintEquation, EqualityProblem, InequalityProblem)
getSingleAccess _ (Single acc) = lift $ return acc
getSingleAccess err _ = lift $ throwError err
-}
          
-- | Odd helper function for getting/asserting the first item of a triple from a singleton list inside a monad transformer (!)
getSingleItem :: MonadTrans m => String -> [(a,b,c)] -> m (Either String) a
getSingleItem _ [(item,_,_)] = lift $ return item
getSingleItem err _ = lift $ throwError err


-- | Given a list of (written,read) expressions, an expression representing the upper array bound, returns either an error
-- (because the expressions can't be handled, typically) or a set of equalities, inequalities and mapping from
-- (unique, munged) variable name to variable-index in the equations.
-- TODO probably want to take this into the PassM monad at some point, to use the Meta in the error message
-- TODO allow "background knowledge" in the form of other equalities and inequalities
makeEquations :: ([A.Expression],[A.Expression]) -> A.Expression -> Either String [(VarMap, (EqualityProblem, InequalityProblem))]
makeEquations (esW,esR) high = makeEquations' >>* uncurry3 (squareAndPair [])
  where
  
    -- | The body of makeEquations; returns the variable mapping, the list of (nx,ex) pairs and a pair
    -- representing the upper and lower bounds of the array (inclusive).    
    makeEquations' :: Either String (VarMap, [ArrayAccess], (EqualityConstraintEquation, EqualityConstraintEquation))
    makeEquations' = do ((v,h),s) <- (flip runStateT) Map.empty $
                           do eqsW <- mapM (makeEquation AAWrite) =<< lift (mapM flatten esW)
                              eqsR <- mapM (makeEquation AARead) =<< lift (mapM flatten esR)
                              high' <- (lift $ flatten high) >>= makeEquation (error "Type irrelevant for upper bound")
                                >>= getSingleAccessItem "Multiple possible upper bounds not supported"
                              return (eqsW ++ eqsR,high')
                        return (s,v,(amap (const 0) h, addConstant (-1) h))
                             
 
  
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
pairEqsAndBounds :: [ArrayAccess] -> (EqualityConstraintEquation, EqualityConstraintEquation) -> [(EqualityProblem, InequalityProblem)]
pairEqsAndBounds items bounds = (concatMap (uncurry pairEqs) . allPairs) items ++ concatMap pairRep items
      where
        pairEqs :: ArrayAccess
          -> ArrayAccess
          -> [(EqualityProblem, InequalityProblem)]
        pairEqs (Single acc) (Single acc') = maybeToList $ pairEqs' acc acc'
        pairEqs (Single acc) (Group accs) = mapMaybe (pairEqs' acc) accs
        pairEqs (Group accs) (Single acc) = mapMaybe (pairEqs' acc) accs
        pairEqs (Group accs) (Group accs') = mapMaybe (uncurry pairEqs') $ product2 (accs,accs')
        pairEqs (Replicated rA rB) acc
          = concatMap (pairEqs acc) rA
        pairEqs acc (Replicated rA rB)
          = concatMap (pairEqs acc) rA
      
        -- Used to pair the items of a single instance of PAR replication with each other
        pairRep :: ArrayAccess -> [(EqualityProblem, InequalityProblem)]
        pairRep (Replicated rA rB) = (concatMap (uncurry pairEqs) $ product2 (rA,rB)) ++ concatMap (uncurry pairEqs) (allPairs rA)
        pairRep _ = []
      
        pairEqs' :: (ArrayAccessType,(EqualityConstraintEquation, EqualityProblem, InequalityProblem))
          -> (ArrayAccessType,(EqualityConstraintEquation, EqualityProblem, InequalityProblem))
          -> Maybe (EqualityProblem, InequalityProblem)
        pairEqs' (AARead,_) (AARead,_) = Nothing
        pairEqs' (_,(ex,eqX,ineqX)) (_,(ey,eqY,ineqY)) = Just ([arrayZipWith' 0 (-) ex ey] ++ eqX ++ eqY, ineqX ++ ineqY ++ getIneqs bounds [ex,ey])
    
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
makeEquation :: ArrayAccessType -> [FlattenedExp] -> StateT VarMap (Either String) ArrayAccess
makeEquation t summedItems
      = do eqs <- process summedItems
           let eqs' = map (transformTriple mapToArray (map mapToArray) (map mapToArray)) eqs
           return $ case eqs' of
             [acc] -> Single (t,acc)
             _ -> Group $ zip (repeat t) eqs'
      where
        process :: [FlattenedExp] -> StateT VarMap (Either String) [(Map.Map Int Integer,[Map.Map Int Integer], [Map.Map Int Integer])]
        process = foldM makeEquation' empty
      
        makeEquation' :: [(Map.Map Int Integer,[Map.Map Int Integer], [Map.Map Int Integer])] -> FlattenedExp -> StateT (VarMap) (Either String) [(Map.Map Int Integer,[Map.Map Int Integer], [Map.Map Int Integer])]
        makeEquation' m (Const n) = return $ add (0,n) m
        makeEquation' m sc@(Scale n v) = varIndex sc >>* (\ind -> add (ind, n) m)
        makeEquation' m mod@(Modulo top bottom)
          = do top' <- process $ Set.toList top
               top'' <- getSingleItem "Modulo or divide not allowed in the numerator of Modulo" top'
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
                   do bottom'' <- getSingleItem "Modulo or divide not allowed in the divisor of Modulo" bottom'
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

makeSize :: ({- Show i, Show e, -} IArray a e, Ix i, Enum i) => (i,i) -> e -> a i e -> a i e
makeSize size def arr = array size [(i,arrayLookupWithDefault def arr i) | i <- [fst size .. snd size]]
    

-- | Given a pair of equation sets, makes all the equations in the lists be the length
-- of the longest equation.  All missing elements are of course given value zero.
squareEquations :: ([Array CoeffIndex Integer],[Array CoeffIndex Integer]) -> ([Array CoeffIndex Integer],[Array CoeffIndex Integer])
squareEquations (eqs,ineqs) = uncurry transformPair (mkPair $ map $ makeSize (0,highest) 0) (eqs,ineqs)
    
      where      
        highest = maximum $ 0 : (concatMap indices $ eqs ++ ineqs)

