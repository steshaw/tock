{-
Tock: a compiler for parallel languages
Copyright (C) 2007--2009  University of Kent

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

module ArrayUsageCheck (
  BackgroundKnowledge(..),
  BK,
  canonicalise,
  checkArrayUsage,
  findRepSolutions,
  FlattenedExp(..),
  fmapFlattenedExp,
  makeEquations,
  makeExpSet,
  ModuloCase(..),
  onlyConst,
  showFlattenedExp,
  VarMap) where

import Control.Monad.Error
import Control.Monad.State
import Data.Array.IArray
import Data.Generics hiding (GT)
import Data.Int
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import qualified AST as A
import CompState
import Errors
import Metadata
import Omega
import OrdAST()
import Pass
import ShowCode
import Types
import UsageCheckUtils
import Utils

-- Each list is a possible set of background knowledge mapping vars to a list
-- of constraints.  So it is a disjunction of map from variables to conjunctions
type BK = [Map.Map Var [BackgroundKnowledge]]
type BK' = [Map.Map Var (Either String (EqualityProblem, InequalityProblem))]

-- | Given a list of replicators, and a set of background knowledge for each
-- access inside the replicator, checks if there are any solutions for a
-- combination of the normal replicator constraints, and the given background
-- knowledge (pairing each set against each other, applying one set to the replicator,
-- and the other to the mirror of the replicator).
--
-- Returns Nothing if no solutions, a String with a counter-example if there
-- are solutions
findRepSolutions :: (CSMR m, MonadIO m) => [(A.Name, A.Replicator)] -> [BK] -> m (Maybe String)
findRepSolutions reps bks
  -- To get the right comparison, we create a SeqItems with all the accesses
  -- Because they are inside a PAR replicator, they will all get compared to each
  -- other with one set of BK applied to i and one applied to i', but they will
  -- never be compared to each other just with the constraints on i (which is not
  -- what we are checking here).  We set the dummy array accesses to all be zero,
  -- which means they can overlap -- but only if there is also a solution to the
  -- replicator background knowledge, which is what this function is trying to
  -- determine.
  = case makeEquations (addReps $ SeqItems [(bk, [makeConstant emptyMeta 0], [])
                                           | bk <- bks]) maxInt of
            Right problems -> do
              probs <- formatProblems [(vm, prob) | (_,vm,prob) <- problems]
              debug $ "Problems in findRepSolutions:\n" ++ probs
              case catMaybes [fmap ((,) i) $ solve p | (i::Integer, p) <- zip [0..] problems] of
                [] -> return Nothing -- No solutions, safe
                xs -> liftM (Just . unlines) $ mapM format xs
            res -> error $ "Unexpected reachability result"
  where
    maxInt = makeConstant emptyMeta $ fromInteger $ toInteger (maxBound :: Int32)

    format (i, ((lx,ly),varMapping,vm,problem))
      = formatSolution varMapping (getCounterEqs vm) >>* (("#" ++ show i ++ ": ") ++)

    addReps = flip (foldl $ flip RepParItem) reps

-- | A check-pass that checks the given ParItems (usually generated from a control-flow graph)
-- for any overlapping array indices.
checkArrayUsage :: forall m. (Die m, CSMR m, MonadIO m) => (Meta, ParItems (BK, UsageLabel)) -> m ()
checkArrayUsage (m,p) = mapM_ (checkIndexes m) $ Map.toList $
    groupArrayIndexes $ fmap (transformPair id nodeVars) p
  where
    getDecl :: UsageLabel -> Maybe String
    getDecl = join . fmap getScopeIn . nodeDecl
      where
        getScopeIn (ScopeIn _ n) = Just n
        getScopeIn _ = Nothing

    
    -- Takes a ParItems Vars, and returns a map from array-variable-name to a list of writes and a list of reads for that array.
    -- Returns (array name, list of written-to indexes, list of read-from indexes)
    groupArrayIndexes :: ParItems (BK, Vars) -> Map.Map String (ParItems (BK, [A.Expression], [A.Expression]))
    groupArrayIndexes = filterByKey . fmap
      (\(bk,vs) -> zipMap (join bk) (makeList $ (Map.keysSet $ writtenVars vs)
        `Set.union` (usedVars vs)) (makeList $ readVars vs))
      where
        join :: b -> Maybe [a] -> Maybe [a] -> Maybe (b, [a],[a])
        join k x y = Just (k, fromMaybe [] x, fromMaybe [] y)
        
        -- Turns a set of variables into a map (from array-name to list of index-expressions)
        makeList :: Set.Set Var -> Map.Map String [A.Expression]
        makeList = Set.fold (maybe id (uncurry $ Map.insertWith (++)) . getArrayIndex) Map.empty
        
        -- Lifts a map (from array-name to expression-lists) inside a ParItems to being a map (from array-name to ParItems of expression lists)
        filterByKey :: ParItems (Map.Map String (BK, [A.Expression], [A.Expression])) -> Map.Map String (ParItems (BK,
          [A.Expression], [A.Expression]))
        filterByKey p = Map.fromList $ map trans keys
          where
            keys :: [String]
            keys = concatMap Map.keys $ flattenParItems p

            trans :: String -> (String, ParItems (BK, [A.Expression], [A.Expression]))
            trans k = (k, fmap (Map.findWithDefault ([], [], []) k) p)
      
        -- Gets the (array-name, indexes) from a Var.
        -- TODO this is quite hacky, and doesn't yet deal with slices and so on:
        getArrayIndex :: Var -> Maybe (String, [A.Expression])
        getArrayIndex (Var (A.SubscriptedVariable _ (A.Subscript _ _ e) (A.Variable _ n)))
          = Just (A.nameName n, [e])
        getArrayIndex _ = Nothing

    -- Checks the given ParItems of writes and reads against each other.  The
    -- String (array-name) and Meta are only used for printing out error messages
    checkIndexes :: Meta -> (String, ParItems (BK, [A.Expression], [A.Expression])) -> m ()
    checkIndexes m (arrName, indexes) = do
      sharedNames <- getCompState >>* csNameAttr
      let declNames = [x | Just x <- fmap (getDecl . snd) $ flattenParItems p]
      when (Map.lookup arrName sharedNames /= Just NameShared && arrName `notElem` declNames) $
        do userArrName <- getRealName (A.Name undefined arrName)
           arrType <- astTypeOf (A.Name undefined arrName)
           arrLength <- case arrType of
             A.Array (A.Dimension d:_) _ -> return d
             -- Unknown dimension, use the maximum value for a (assumed 32-bit for INT) integer:
             A.Array (A.UnknownDimension:_) _ -> return $ makeConstant m $ fromInteger $ toInteger (maxBound :: Int32)
             -- It's not an array:
             _ -> dieP m $ "Cannot usage check array \"" ++ userArrName ++ "\"; found to be of type: " ++ show arrType
           case makeEquations indexes arrLength of
               Left err -> dieP m $ "Could not work with array indexes for array \"" ++ userArrName ++ "\": " ++ err
               Right [] -> return () -- No problems to work with
               Right problems -> do
                 probs <- formatProblems [(vm, prob) | (_,vm,prob) <- problems]
                 debug $ "Problems in checkArrayUsage:\n" ++ probs
                 case mapMaybe solve problems of
                   -- No solutions; no worries!
                   [] -> return ()
                   (((lx,ly),varMapping,vm,problem):_) ->
                     do sol <- formatSolution varMapping (getCounterEqs vm)
                        cx <- showCode (fst lx)
                        cy <- showCode (fst ly)
--                        liftIO $ putStrLn $ "Found solution for problem: " ++ probs
--                         ++ show p
--                        liftIO $ putStrLn $ "Succeeded on problem: " ++ prob
--                        allProbs <- concatMapM (\(_,_,p) -> formatProblem varMapping p >>* (++ "\n#\n")) problems
--                        svm <- mapM (showFlattenedExp showCode) $ Map.keys varMapping
--                        liftIO $ putStrLn $ "All problems: " ++ allProbs ++ "\n" ++ (concat $ intersperse " ; " $ svm)
                        dieP m $ "Indexes of array \"" ++ userArrName ++ "\" "
                                 ++ "(\"" ++ cx ++ "\" and \"" ++ cy ++ "\") could overlap"
                                 ++ if sol /= "" then " when: " ++ sol else ""

    -- TODO this is surely defined elsewhere already?
    getRealName :: A.Name -> m String
    getRealName n = lookupName n >>* A.ndOrigName

formatProblems :: CSMR m => [(VarMap, (EqualityProblem, InequalityProblem))] -> m String
formatProblems probs = do formatted <- mapM (uncurry formatProblem) probs
                          return $ concat [addNum i (lines p) | (p, i) <- zip formatted [0..]]
  where
    addNum :: Int -> [String] -> String
    addNum i [] = ""
    addNum i (p:ps) = unlines $
      ("#" ++ show i ++ (if length (show i) == 1 then " :" else ":")
        ++ p) : map ("    " ++) ps

-- | Formats an entire problem ready to print it out half-legibly for debugging purposes
formatProblem :: forall m. CSMR m => VarMap -> (EqualityProblem, InequalityProblem) -> m String
formatProblem varToIndex (eq, ineq)
      = do feqs <- mapM (showWithConst "=") $ eq
           fineqs <- mapM (\e -> if allNegative e
                                   then showWithConst "<=" (negateAll e)
                                   else showWithConst ">=" e) $ ineq
           return $ unlines $ feqs ++ fineqs
      where
        --Returns true if all the variable coefficients are negative (ignoring
        -- the constant term)
        allNegative :: Array CoeffIndex Integer -> Bool
        allNegative = all (<= 0) . tail . elems
        negateAll :: Array CoeffIndex Integer -> Array CoeffIndex Integer
        negateAll = amap negate
        
        showWithConst :: String -> Array CoeffIndex Integer -> m String
        showWithConst op item = do text <- showEq item
                                   return $
                                     (if text == "" then "0" else text)
                                       ++ " " ++ op ++ " " ++ show (negate $ item ! 0)

        showEq :: Array CoeffIndex Integer -> m String
        showEq = liftM (concat . intersperse " + ") . mapM showItem . filter ((/= 0) . snd) . tail . assocs

        showItem :: (CoeffIndex, Integer) -> m String
        showItem (n, a) = case find ((== n) . snd) $ Map.assocs varToIndex of
          Just (exp,_) -> showFlattenedExp showCode exp >>* (mult ++)
          Nothing -> return "<unknown>"
          where
            mult = case a of
              1 -> ""
              -1 -> "-"
              _ -> show a ++ "*"

-- | Solves the problem and munges the arguments and results into a useful order
solve :: (labels,vm,(EqualityProblem,InequalityProblem)) ->
  Maybe (labels,vm,VariableMapping,(EqualityProblem,InequalityProblem))
solve (ls,vm,(eq,ineq)) = case solveProblem eq ineq of
      Nothing -> Nothing
      Just vm' -> Just (ls,vm,vm',(eq,ineq))

-- | Formats a solution (not a problem, just the solution) ready to print it out for the user
formatSolution :: (CSMR m, Monad m) => VarMap -> Map.Map CoeffIndex Integer -> m String
formatSolution varToIndex indexToConst
 = do names <- mapM valOfVar $ Map.assocs varToIndex
      return $ concat $ intersperse " , " $ catMaybes names
      where
        valOfVar (varExp,k) = case Map.lookup k indexToConst of 
          Nothing -> return Nothing
          Just val -> do varExp' <- showFlattenedExp showCode varExp
                         return $ Just $ varExp' ++ " = " ++ show val


showFlattenedExpSet :: Monad m => (A.Expression -> m String) -> Set.Set FlattenedExp -> m String
showFlattenedExpSet showExp s = liftM concat $ sequence $ intersperse (return " + ") $ map (showFlattenedExp showExp) $ Set.toList s

-- Shows a FlattenedExp legibly by looking up real names for variables, and formatting things.
-- The output for things involving modulo might be a bit odd, but there isn't really anything 
-- much that can be done about that
showFlattenedExp :: Monad m => (A.Expression -> m String) -> FlattenedExp -> m String
showFlattenedExp _ (Const n) = return $ show n
showFlattenedExp showExp (Scale n (e,vi))
  = do vn' <- showExp e >>* (++ replicate vi '\'')
       return $ showScale vn' n
showFlattenedExp showExp (Modulo n top bottom)
  = do top' <- showFlattenedExpSet showExp top
       bottom' <- showFlattenedExpSet showExp bottom
       case onlyConst (Set.toList bottom) of
         Just _  -> return $ showScale ("(" ++ top' ++ " / " ++ bottom' ++ ")") (-n)
         Nothing -> return $ showScale ("((" ++ top' ++ " REM " ++ bottom' ++ ") - " ++ top' ++ ")") n
showFlattenedExp showExp (Divide n top bottom)
  = do top' <- showFlattenedExpSet showExp top
       bottom' <- showFlattenedExpSet showExp bottom
       return $ showScale ("(" ++ top' ++ " / " ++ bottom' ++ ")") n

showScale :: String -> Integer -> String
showScale s n =
           case n of
             1  -> s
             -1 -> "-" ++ s
             _  -> (show n) ++ "*" ++ s

-- | A type for inside makeEquations:
data FlattenedExp
  = Const Integer 
    -- ^ A constant
  | Scale Integer (A.Expression, Int)
    -- ^ A variable and coefficient.  The first argument is the coefficient
    -- The second part of the pair is for sub-indexing (or "priming") variables.
    -- For example, replication is done by checking the replicated variable "i"
    -- against a sub-indexed (with "1") version (denoted "i'").  The sub-index
    -- is what differentiates i from i', given that they are technically the
    -- same A.Variable
  | Modulo Integer (Set.Set FlattenedExp) (Set.Set FlattenedExp)
    -- ^ A modulo, with a coefficient\/scale and given top and bottom (in that order)
  | Divide Integer (Set.Set FlattenedExp) (Set.Set FlattenedExp)
    -- ^ An integer division, with a coefficient\/scale and the given top and bottom (in that order)

instance Eq FlattenedExp where
  a == b = EQ == compare a b

-- | A straightforward comparison for FlattenedExp that compares while ignoring
-- the value of a const @(Const 3 == Const 5)@ and the value of a scale
-- @(Scale 1 (v,0)) == (Scale 3 (v,0))@, although note that @(Scale 1 (v,0)) \/= (Scale 1 (v,1))@.
instance Ord FlattenedExp where
  compare (Const _) (Const _) = EQ
  compare (Const _) _ = LT
  compare _ (Const _) = GT
  compare (Scale _ (lv,li)) (Scale _ (rv,ri)) = combineCompare [compare lv rv, compare li ri]
  compare (Scale {}) _ = LT
  compare _ (Scale {}) = GT
  compare (Modulo _ ltop lbottom) (Modulo _ rtop rbottom)
    = combineCompare [compare ltop rtop, compare lbottom rbottom]
  compare (Modulo {}) _ = LT
  compare _ (Modulo {}) = GT
  compare (Divide _ ltop lbottom) (Divide _ rtop rbottom)
    = combineCompare [compare ltop rtop, compare lbottom rbottom]

-- | Checks if an expression list contains only constants.  Returns Just (the aggregate constant) if so,
-- otherwise returns Nothing.
onlyConst :: [FlattenedExp] -> Maybe Integer
onlyConst [] = Just 0
onlyConst ((Const n):es) = liftM2 (+) (return n) $ onlyConst es
onlyConst _ = Nothing

fmapFlattenedExp :: (A.Expression -> A.Expression) -> FlattenedExp -> FlattenedExp
fmapFlattenedExp f x@(Const _) = x
fmapFlattenedExp f (Scale n (e, i)) = Scale n (f e, i)
fmapFlattenedExp f (Modulo n top bottom)
  = Modulo n (Set.map (fmapFlattenedExp f) top) (Set.map (fmapFlattenedExp f) bottom)
fmapFlattenedExp f (Divide n top bottom)
  = Divide n (Set.map (fmapFlattenedExp f) top) (Set.map (fmapFlattenedExp f) bottom)

-- | A data type representing an array access.  Each triple is (index, extra-equalities, extra-inequalities).
-- A Single item can be paired with every other access.
-- Each item of a Group cannot be paired with each other, but can be paired with each other access.
-- With a Replicated, each item in the left branch can be paired with each item in the right branch.
-- Each item in the left branch can be paired with each other, and each item in the left branch can
-- be paired with all other items.
data ArrayAccess label =
  Group [(label, ArrayAccessType, (EqualityConstraintEquation, EqualityProblem, InequalityProblem))]
  | Replicated [ArrayAccess label] [ArrayAccess label]

-- | A simple data type for denoting whether an array access is a read or a write
data ArrayAccessType = AAWrite | AARead

-- | Transforms the ParItems (from the control-flow graph) into the more suitable ArrayAccess
-- data type used by this array usage checker.
parItemToArrayAccessM :: Monad m =>
  (  [((A.Name, A.Replicator), Bool)] -> 
     a ->
     m [(label, ArrayAccessType, (EqualityConstraintEquation, EqualityProblem, InequalityProblem))]
  ) -> 
  ParItems a -> 
  m ([ArrayAccess label], [A.Name])
parItemToArrayAccessM f (SeqItems xs)
  -- Each sequential item is a group of one:
  = do aas <- sequence [concatMapM (f []) xs >>* Group]
       return (aas, [])
parItemToArrayAccessM f (ParItems ps)
   = liftM (transformPair concat concat . unzip) $ mapM (parItemToArrayAccessM f) ps
parItemToArrayAccessM f (RepParItem rep p) 
  = do (normal, otherReps) <- parItemToArrayAccessM (\reps -> f ((rep,False):reps)) p
       mirror <- liftM fst $ parItemToArrayAccessM (\reps -> f ((rep,True):reps)) p
       return ([Replicated normal mirror], fst rep : otherReps)

-- | Turns a list of expressions (which may contain many constants, or duplicated variables)
-- into a set of expressions with at most one constant term, and at most one appearance
-- of a any variable, or distinct modulo\/division of variables.
-- If there is any problem (specifically, nested modulo or divisions) an error will be returned instead
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

    addScale :: Integer -> (A.Expression,Int) -> FlattenedExp -> Set.Set FlattenedExp -> Maybe (Set.Set FlattenedExp)
    addScale x (lv,li) (Scale n (rv,ri)) s
      | (EQ == compare lv rv) && (li == ri) = Just $ Set.insert (Scale (x + n) (rv,ri)) s
      | otherwise = Nothing
    addScale _ _ _ _ = Nothing

-- | A map from an item (a FlattenedExp, which may be a variable, or modulo\/divide item) to its coefficient in the problem.
type VarMap = Map.Map FlattenedExp CoeffIndex

-- | Background knowledge about a problem; either an equality or an inequality.
data BackgroundKnowledge
  = Equal A.Expression A.Expression
    | LessThanOrEqual A.Expression A.Expression
    | RepBoundsIncl A.Variable A.Expression A.Expression
  deriving (Typeable, Data)

instance Show BackgroundKnowledge where
  show (Equal e e') = showOccam e ++ " = " ++ showOccam e'
  show (LessThanOrEqual e e') = showOccam e ++ " <= " ++ showOccam e'
  show (RepBoundsIncl v e e')
    = showOccam e ++ " <= " ++ showOccam v ++ " <= " ++ showOccam e'

-- | The names relate to the equations given in my Omega Test presentation.
-- X is the top, Y is the bottom, A is the other var (x REM y = x + a)
data ModuloCase =
   XZero
 | XPos | XNeg -- these two are for constant divisor, all the ones below are for variable divisor
 | XPosYPosAZero | XPosYPosANonZero
 | XPosYNegAZero | XPosYNegANonZero
 | XNegYPosAZero | XNegYPosANonZero
 | XNegYNegAZero | XNegYNegANonZero
 deriving (Show, Eq, Ord)

-- | Transforms background knowledge into problems
-- TODO allow modulo in background knowledge
transformBK :: ([FlattenedExp] -> [FlattenedExp]) -> BackgroundKnowledge -> StateT VarMap (Either String) (EqualityProblem,InequalityProblem)
transformBK f (Equal eL eR)   = do eL' <- makeSingleEq f eL "background knowledge"
                                   eR' <- makeSingleEq f eR "background knowledge"
                                   let e = addEq eL' (amap negate eR')
                                   return ([e],[])
transformBK f (LessThanOrEqual eL eR)
      = do eL' <- makeSingleEq f eL "background knowledge"
           eR' <- makeSingleEq f eR "background knowledge"
           -- eL <= eR implies eR - eL >= 0
           let e = addEq (amap negate eL') eR'
           return ([],[e])
transformBK f (RepBoundsIncl v low high)
  = do eLow <- makeSingleEq f low "background knowledge, lower bound"
       eHigh <- makeSingleEq f high "background knowledge, upper bound"
       -- v <= eH implies eH - v >= 0
       -- eL <= v implies v - eL >= 0
       ev <- makeEquation v ([], id) (error "Irrelevant type") [Scale 1 (A.ExprVariable emptyMeta v, 0)]
         >>= getSingleAccessItem ("Modulo or divide impossible")
       ev' <- makeEquation v ([], id) (error "Irrelevant type") [Scale 1 (A.ExprVariable emptyMeta v, 1)]
         >>= getSingleAccessItem ("Modulo or divide impossible")
       return ([], [ addEq (amap negate ev) eHigh
                   , addEq (amap negate ev') eHigh
                   , addEq (amap negate eLow) ev
                   , addEq (amap negate eLow) ev'
                   ])

transformBKList :: ([FlattenedExp] -> [FlattenedExp]) -> [BackgroundKnowledge] -> StateT VarMap (Either String) (EqualityProblem,InequalityProblem)
transformBKList f bk = mapM (transformBK f) bk >>* foldl accumProblem ([],[])

-- | Turns a single expression into an equation-item.  An error is given if the resulting 
-- expression is anything complicated (for example, modulo or divide)
makeSingleEq :: ([FlattenedExp] -> [FlattenedExp]) -> A.Expression -> String -> StateT VarMap (Either String) EqualityConstraintEquation
makeSingleEq f e desc = (lift (flatten e) >>* f) >>= makeEquation e ([{-TODO-}],
  f) (error $ "Type is irrelevant for " ++ desc)
  >>= getSingleAccessItem ("Modulo or Divide not allowed in " ++ desc
        ++ "(while processing: " ++ showOccam e ++ ")")

-- | A helper function for joining two problems
accumProblem :: (EqualityProblem,InequalityProblem) -> (EqualityProblem,InequalityProblem) -> (EqualityProblem,InequalityProblem)
accumProblem = concatPair


-- | Given a list of (written,read) expressions, an expression representing the upper array bound, returns either an error
-- (because the expressions can't be handled, typically) or a set of equalities, inequalities and mapping from
-- (unique, munged) variable name to variable-index in the equations.
--
-- The general strategy is as follows.
-- For every array index (here termed an "access"), we transform it into
-- the usual @[FlattenedExp]@ using the flatten function.  Then we also transform
-- any access that is in the mirror-side of a Replicated item into its mirrored version
-- where each i is changed into i\'.  This is done by using @vi=(variable "i",0)@
-- (in @Scale _ vi@) for the plain (normal) version, and @vi=(variable "i",1)@
-- for the prime (mirror) version.
--
-- Then the equations have bounds added.  The rules are fairly simple; if
-- any of the transformed EqualityConstraintEquation (or related equalities or inequalities) representing an access
-- have a non-zero i (and\/or i\'), the bound for that variable is added.
-- So for example, an expression like i = i\' + 3 would have the bounds for
-- both i and i\' added (which would be near-identical, e.g. 1 <= i <= 6 and
-- 1 <= i\' <= 6).  We have to check the equalities and inequalities because
-- when processing modulo, for the i REM y == 0 option, i will not appear in
-- the index itself (which will be 0) but will appear in the surrounding
-- constraints, and we still want to add the replication bounds.
--
-- The remainder of the work (correctly pairing equations) is done by
-- squareAndPair.
--
-- TODO probably want to take this into the PassM monad at some point, to use the Meta in the error message
makeEquations :: ParItems (BK, [A.Expression], [A.Expression]) -> A.Expression ->
  Either String [(((A.Expression, [ModuloCase]), (A.Expression, [ModuloCase])), VarMap, (EqualityProblem, InequalityProblem))]
makeEquations accesses bound
  = do ((v,h,repVarIndexes, allReps),s) <- (flip runStateT) Map.empty $
          do ((accesses', allReps),repVars) <- flip runStateT [] $ parItemToArrayAccessM mkEq accesses
             high <- makeSingleEq id bound "upper bound"
             return (accesses', high, nub repVars, allReps)
       squareAndPair (lookupBK allReps) (\(x,y,_) -> (x,y)) repVarIndexes s v (amap (const 0) h, addConstant (-1) h)

  where
    lookupBK :: [A.Name] -> (A.Expression, [ModuloCase], BK') -> Either String
      [(EqualityProblem, InequalityProblem)]
    lookupBK reps (e,_,bk) = mapM (foldl (liftM2 accumProblem) (return ([],[])) . map snd .
      filter (\(v,_) -> v `elem` vs || v `elem` reps') . Map.toList) bk
      where
        reps' :: [Var]
        reps' = map (Var . A.Variable emptyMeta) reps
        vs :: [Var]
        vs = map Var $ listify (const True :: A.Variable -> Bool) e
    
    -- | A front-end to the setIndexVar' function
    setIndexVar :: A.Variable -> Int -> [FlattenedExp] -> [FlattenedExp]
    setIndexVar tv ti = map (setIndexVar' tv ti)
  
    -- | Sets the sub-index of the specified variable throughout the expression
    setIndexVar' :: A.Variable -> Int -> FlattenedExp -> FlattenedExp
    setIndexVar' tv ti s@(Scale n (v,_))
      | EQ == compare (A.ExprVariable emptyMeta tv) v = Scale n (v,ti)
      | otherwise = s
    setIndexVar' tv ti (Modulo n top bottom) = Modulo n top' bottom'
      where
        top' = Set.map (setIndexVar' tv ti) top
        bottom' = Set.map (setIndexVar' tv ti) bottom
    setIndexVar' tv ti (Divide n top bottom) = Divide n top' bottom'
      where
        top' = Set.map (setIndexVar' tv ti) top
        bottom' = Set.map (setIndexVar' tv ti) bottom
    setIndexVar' _ _ e = e

    -- | Given a list of replicators (marked enabled\/disabled by a flag), the writes and reads, 
    -- turns them into a single list of accesses with all the relevant information.  The writes and reads
    -- can be grouped together because they are differentiated by the ArrayAccessType in the result
    mkEq :: [((A.Name, A.Replicator), Bool)] ->
            (BK, [A.Expression], [A.Expression]) ->
             StateT [(CoeffIndex, CoeffIndex)]
               (StateT VarMap (Either String))
                 [((A.Expression, [ModuloCase], BK'), ArrayAccessType, (EqualityConstraintEquation, EqualityProblem, InequalityProblem))]
    mkEq reps (bk, ws, rs) = do repVarEqs <- mapM (liftF makeRepVarEq) reps
                                concatMapM (mkEq' repVarEqs) (ws' ++ rs')
      where
        ws' = zip (repeat AAWrite) ws
        rs' = zip (repeat AARead) rs
        
        makeRepVarEq :: ((A.Name, A.Replicator), Bool) -> StateT VarMap (Either String) (A.Variable, EqualityConstraintEquation, EqualityConstraintEquation)
        makeRepVarEq ((varName, A.For m from for _), _)
          = do from' <- makeSingleEq id from "replication start"
               upper <- makeSingleEq id (A.Dyadic m A.Subtr (A.Dyadic m A.Add for from) (makeConstant m 1)) "replication count"
               return (A.Variable m varName, from', upper)

        mkEq' :: [(A.Variable, EqualityConstraintEquation, EqualityConstraintEquation)] ->
                 (ArrayAccessType, A.Expression) ->
                 StateT [(CoeffIndex,CoeffIndex)]
                   (StateT VarMap (Either String))
                     [((A.Expression, [ModuloCase], BK'), ArrayAccessType, (EqualityConstraintEquation, EqualityProblem, InequalityProblem))]
        mkEq' repVarEqs (aat, e) 
                       = do f <- lift . lift $ flatten e
                            mirrorFunc <- liftM foldFuncs $ mapM mirrorFlaggedVar reps
                            g <- lift $ makeEquation e (bk, mirrorFunc) aat (mirrorFunc f)
                            case g of
                              Group g' -> return g'
                              _ -> throwError "Replicated group found unexpectedly"

    -- | Turns all instances of the variable from the given replicator into their primed version in the given expression
    mirrorFlaggedVar :: ((A.Name, A.Replicator),Bool) -> StateT [(CoeffIndex,CoeffIndex)] (StateT VarMap (Either String)) ([FlattenedExp] -> [FlattenedExp])
    mirrorFlaggedVar (_,False) = return id
    mirrorFlaggedVar ((varName, A.For m from for _), True)
      = do varIndexes <- lift $ seqPair (varIndex (Scale 1 (A.ExprVariable emptyMeta var,0)), varIndex (Scale 1 (A.ExprVariable emptyMeta var,1)))
           modify (varIndexes :)
           return $ setIndexVar var 1
      where
        var = A.Variable m varName

-- Note that in all these functions, the divisor should always be positive!

canonicalise :: A.Expression -> A.Expression
canonicalise e@(A.Dyadic m op _ _) | op == A.Add || op == A.Mul
  = foldl1 (A.Dyadic m op) $ sort $ gatherTerms op e
  where
    gatherTerms :: A.DyadicOp -> A.Expression -> [A.Expression]
    gatherTerms op (A.Dyadic _ op' lhs rhs) | op == op'
      = gatherTerms op lhs ++ gatherTerms op rhs
    gatherTerms _ e = [canonicalise e]
canonicalise (A.Dyadic m op lhs rhs)
  = A.Dyadic m op (canonicalise lhs) (canonicalise rhs)
canonicalise (A.Monadic m op rhs)
  = A.Monadic m op (canonicalise rhs)
canonicalise e = e

flatten :: A.Expression -> Either String [FlattenedExp]
flatten (A.Literal _ _ (A.IntLiteral _ n)) = return [Const (read n)]
flatten e@(A.Dyadic m op lhs rhs)
  | op == A.Add   = combine' (flatten lhs) (flatten rhs)
  | op == A.Subtr = combine' (flatten lhs) (mapM (scale (-1)) =<< flatten rhs)
  | op == A.Mul   = multiplyOut' (flatten lhs) (flatten rhs)
  | op == A.Rem   = liftM2L (Modulo 1) (flatten lhs) (flatten rhs)
  | op == A.Div   = do rhs' <- flatten rhs
                       case onlyConst rhs' of
                         Just _ -> liftM2L (Divide 1) (flatten lhs) (return rhs')
                         -- Can't deal with variable divisors, leave expression as-is:
                         Nothing -> return [Scale 1 (canonicalise e,0)]
  where
--    liftM2L :: (Ord a, Ord b, Monad m) => (Set.Set a -> Set.Set b -> c) -> m [a] -> m [b] -> m [c]
    liftM2L f x y = liftM singleton $ liftM2 f (x >>= makeExpSet) (y >>= makeExpSet)

    multiplyOut' :: Either String [FlattenedExp] -> Either String [FlattenedExp] -> Either String [FlattenedExp]
    multiplyOut' x y = do {x' <- x; y' <- y; multiplyOut x' y'}
    
    multiplyOut :: [FlattenedExp] -> [FlattenedExp] -> Either String [FlattenedExp]
    multiplyOut lhs rhs = mapM (uncurry mult) pairs 
      where
        pairs = product2 (lhs,rhs)

        mult :: FlattenedExp -> FlattenedExp -> Either String FlattenedExp
        mult (Const x) e = scale x e
        mult e (Const x) = scale x e
        mult lhs rhs
          = do lhs' <- backToEq lhs
               rhs' <- backToEq rhs
               return $ (Scale 1 (canonicalise $ A.Dyadic emptyMeta A.Mul lhs' rhs', 0))
    
        backScale :: Integer -> A.Expression -> A.Expression
        backScale 1 = id
        backScale n = canonicalise . A.Dyadic emptyMeta A.Mul (makeConstant emptyMeta (fromInteger n))
    
        backToEq :: FlattenedExp -> Either String A.Expression
        backToEq (Const c) = return $ makeConstant emptyMeta (fromInteger c)
        backToEq (Scale n (e,0)) = return $ backScale n e
        backToEq (Modulo n t b)
          | Set.null t || Set.null b = throwError "Modulo had empty top or bottom"
          | otherwise = do t' <- mapM backToEq $ Set.toList t
                           b' <- mapM backToEq $ Set.toList b
                           return $
                            (backScale n $ A.Dyadic emptyMeta A.Rem
                              (foldl1 (A.Dyadic emptyMeta A.Add) t')
                              (foldl1 (A.Dyadic emptyMeta A.Add) b'))
        backToEq (Divide n t b)
          | Set.null t || Set.null b = throwError "Divide had empty top or bottom"
          | otherwise = do t' <- mapM backToEq $ Set.toList t
                           b' <- mapM backToEq $ Set.toList b
                           return $
                            (backScale n $ A.Dyadic emptyMeta A.Div
                              (foldl1 (A.Dyadic emptyMeta A.Add) t')
                              (foldl1 (A.Dyadic emptyMeta A.Add) b'))
    
    -- | Scales a flattened expression by the given integer scaling.
    scale :: Integer -> FlattenedExp -> Either String FlattenedExp
    scale sc (Const n) = return $ Const (n * sc)
    scale sc (Scale n v) = return $ Scale (n * sc) v
    scale sc (Modulo n t b) = return $ Modulo (n * sc) t b
    scale sc (Divide n t b) = return $ Divide (n * sc) t b

    -- | An easy way of applying combine to two monadic returns
    combine' :: Either String [FlattenedExp] -> Either String [FlattenedExp] -> Either String [FlattenedExp]
    combine' = liftM2 combine
    
    -- | Combines (adds) two flattened expressions.
    combine :: [FlattenedExp] -> [FlattenedExp] -> [FlattenedExp]
    combine = (++)
flatten e = return [Scale 1 (canonicalise e,0)]

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
  (label -> Either String [(EqualityProblem, InequalityProblem)]) ->
  (label -> labelStripped) ->
  [(CoeffIndex, CoeffIndex)] ->
  VarMap ->
  [ArrayAccess label] ->
  (EqualityConstraintEquation, EqualityConstraintEquation) ->
  Either String [((labelStripped, labelStripped), VarMap, (EqualityProblem, InequalityProblem))] 
squareAndPair lookupBK strip repVars s v lh
  = concatMapM id
    [let f ((bkEqA, bkIneqA), (bkEqB, bkIneqB))
           = (transformPair strip strip labels,
              s,
              squareEquations (nub (bkEqA ++ bkEqB) ++ eq,
              nub (bkIneqA ++ bkIneqB) ++ ineq ++ concat (applyAll (eq,ineq) (map addExtra repVars))))
         bk = case liftM2 (curry product2) (lookupBK (fst labels)) (lookupBK (snd labels)) of
                Right [] -> Right [(([],[]),([],[]))] -- No BK
                xs -> xs
    in bk >>* map f
    | (labels, eq,ineq) <- pairEqsAndBounds v lh
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
       -- prime >= plain + 1  (prime - plain - 1 >= 0)
       = [mapToArray $ Map.fromList [(prime,1), (plain,-1), (0, -1)]]

getSingleAccessItem :: MonadTrans m => String -> ArrayAccess label -> m (Either String) EqualityConstraintEquation
getSingleAccessItem _ (Group [(_,_,(acc,_,_))]) = lift $ return acc
getSingleAccessItem err _ = lift $ throwError err

-- | Odd helper function for getting\/asserting the first item of a triple from a singleton list inside a monad transformer (!)
getSingleItem :: MonadTrans m => String -> [(a,b,c)] -> m (Either String) a
getSingleItem _ [(item,_,_)] = lift $ return item
getSingleItem err _ = lift $ throwError err

-- | Finds the index associated with a particular variable; either by finding an existing index
-- or allocating a new one.
varIndex :: FlattenedExp -> StateT (VarMap) (Either String) Int
varIndex (Scale _ (e,vi))
      = do st <- get
           let (st',ind) = case Map.lookup (Scale 1 (e,vi)) st of
                             Just val -> (st,val)
                             Nothing -> let newId = (1 + (maximum $ 0 : Map.elems st)) in
                                        (Map.insert (Scale 1 (e,vi)) newId st, newId)
           put st'
           return ind
varIndex mod@(Modulo _ top bottom)
      = do st <- get
           let (st',ind) = case Map.lookup mod st of
                             Just val -> (st,val)
                             Nothing -> let newId = (1 + (maximum $ 0 : Map.elems st)) in
                                        (Map.insert mod newId st, newId)
           put st'
           return ind
varIndex div@(Divide _ top bottom)
      = do st <- get
           let (st',ind) = case Map.lookup div st of
                             Just val -> (st,val)
                             Nothing -> let newId = (1 + (maximum $ 0 : Map.elems st)) in
                                        (Map.insert div newId st, newId)
           put st'
           return ind

-- | Pairs all possible combinations of the list of equations.
pairEqsAndBounds :: [ArrayAccess label] -> (EqualityConstraintEquation, EqualityConstraintEquation) -> [((label,label),EqualityProblem, InequalityProblem)]
pairEqsAndBounds items bounds = (concatMap (uncurry pairEqs) . allPairs) items ++ concatMap pairRep items
      where
        pairEqs :: ArrayAccess label
          -> ArrayAccess label
          -> [((label,label),EqualityProblem, InequalityProblem)]
        pairEqs (Group accs) (Group accs') = mapMaybe (uncurry pairEqs'') $ product2 (accs,accs')
        pairEqs (Replicated rA rB) lacc
          = concatMap (pairEqs lacc) rA
        pairEqs lacc (Replicated rA rB)
          = concatMap (pairEqs lacc) rA
      
        -- Used to pair the items of a single instance of PAR replication with each other
        pairRep :: ArrayAccess label -> [((label,label),EqualityProblem, InequalityProblem)]
        pairRep (Replicated rA rB) =  concatMap (uncurry pairEqs) (product2 (rA,rB)) 
                                     ++ concatMap (uncurry pairEqs) (allPairs rA)
        pairRep _ = []
        
        pairEqs'' :: (label, ArrayAccessType,(EqualityConstraintEquation, EqualityProblem, InequalityProblem))
          -> (label, ArrayAccessType,(EqualityConstraintEquation, EqualityProblem, InequalityProblem))
          -> Maybe ((label,label), EqualityProblem, InequalityProblem)
        pairEqs'' (lx,x,x') (ly,y,y') = case pairEqs' (x,x') (y,y') of
          Just (eq,ineq) -> Just ((lx,ly),eq,ineq)
          Nothing -> Nothing
      
        pairEqs' :: (ArrayAccessType,(EqualityConstraintEquation, EqualityProblem, InequalityProblem))
          -> (ArrayAccessType,(EqualityConstraintEquation, EqualityProblem, InequalityProblem))
          -> Maybe (EqualityProblem, InequalityProblem)
        pairEqs' (AARead,_) (AARead,_) = Nothing
        pairEqs' (_,(ex,eqX,ineqX)) (_,(ey,eqY,ineqY)) = Just ([arrayZipWith' 0 (-) ex ey] ++ eqX ++ eqY, ineqX ++ ineqY ++ getIneqs bounds [ex,ey])

addEq :: EqualityConstraintEquation -> EqualityConstraintEquation -> EqualityConstraintEquation
addEq = arrayZipWith' 0 (+)
    
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

justState :: Error e => StateT s (Either e) a -> StateT s (Either e) (Either e a)
justState m = do st <- get
                 let (x, st') = case runStateT m st of
                                  Left err -> (Left err, st)
                                  Right (x, st') -> (Right x, st')
                 put st'
                 return x
    
-- | Given an expression, forms equations (and accompanying additional equation-sets) and returns it
makeEquation :: label -> (BK, [FlattenedExp] -> [FlattenedExp]) -> ArrayAccessType -> [FlattenedExp] -> StateT VarMap (Either String) (ArrayAccess (label,[ModuloCase],
  BK'))
makeEquation l (bk, bkF) t summedItems
      = do eqs <- process summedItems
           bk' <- mapM (mapMapM (justState . transformBKList bkF)) bk
           let eqs' = map (transformQuad id mapToArray (map mapToArray) (map mapToArray)) eqs :: [([ModuloCase], EqualityConstraintEquation, EqualityProblem, InequalityProblem)]
           return $ Group [((l,c,bk'),t,(e0,e1,e2)) | (c,e0,e1,e2) <- eqs']
      where
        process :: [FlattenedExp] -> StateT VarMap (Either String) [([ModuloCase], Map.Map Int Integer,[Map.Map Int Integer], [Map.Map Int Integer])]
        process = foldM makeEquation' empty
      
        makeEquation' :: [([ModuloCase], Map.Map Int Integer,[Map.Map Int Integer], [Map.Map Int Integer])] ->
                         FlattenedExp ->
                         StateT (VarMap) (Either String)
                           [([ModuloCase], Map.Map Int Integer,[Map.Map Int Integer], [Map.Map Int Integer])]
        makeEquation' m (Const n) = return $ add (0,n) m
        makeEquation' m sc@(Scale n v) = varIndex sc >>* (\ind -> add (ind, n) m)
        makeEquation' m mod@(Modulo n top bottom)
          = do top' <- process (Set.toList top) >>* map (\(_,a,b,c) -> (a,b,c))
               top'' <- getSingleItem "Modulo or divide not allowed in the numerator of Modulo" top'
               bottom' <- process (Set.toList bottom) >>* map (\(_,a,b,c) -> (a,b,c))
               modIndex <- varIndex mod
               case onlyConst (Set.toList bottom) of
                 Just bottomConst -> 
                   let add_x_plus_my = zipMap plus top'' . zipMap plus (Map.fromList [(modIndex, abs bottomConst)]) in
                    -- Adds n*(x + my)
                   let add_n_x_plus_my = zipMap plus (Map.map (*n) top'') . zipMap plus (Map.fromList [(modIndex, n * abs bottomConst)]) in
                   return $
                     -- The zero option (x = 0, x REM y = 0):
                   ( map (transformQuad (++ [XZero]) id (++ [top'']) id) m)
                   ++
                     -- The top-is-positive option:
                   ( map (transformQuad (++ [XPos]) add_n_x_plus_my id (++
                      -- x >= 1
                      [zipMap plus (Map.fromList [(0,-1)]) top''
                      -- m <= 0
                      ,Map.fromList [(modIndex,-1)]
                      -- x + my + 1 - |y| <= 0
                      ,Map.map negate $ add_x_plus_my $ Map.fromList [(0,1 - abs bottomConst)]
                      -- x + my >= 0
                      ,add_x_plus_my $ Map.empty])
                     ) m) ++
                    -- The top-is-negative option:
                   ( map (transformQuad (++ [XNeg]) add_n_x_plus_my id (++
                      -- x <= -1
                      [add' (0,-1) $ Map.map negate top''
                      -- m >= 0
                      ,Map.fromList [(modIndex,1)]
                      -- x + my - 1 + |y| >= 0
                      ,add_x_plus_my $ Map.fromList [(0,abs bottomConst - 1)]
                      -- x + my <= 0
                      ,Map.map negate $ add_x_plus_my Map.empty])
                     ) m)
                 _ ->
                   do bottom'' <- getSingleItem "Modulo or divide not allowed in the divisor of Modulo" bottom'
                      return $
                        -- The zero option (x = 0, x REM y = 0):
                        (map (transformQuad (++ [XZero]) id (++ [top'']) id) m)
                        -- The rest:
                        ++ twinItems True True n (top'', modIndex) bottom''
                        ++ twinItems True False n (top'', modIndex) bottom''
                        ++ twinItems False True n (top'', modIndex) bottom''
                        ++ twinItems False False n (top'', modIndex) bottom''
          where
            -- Each pair for modulo (variable divisor) depending on signs of x and y (in x REM y):
            twinItems :: Bool -> Bool -> Integer -> (Map.Map Int Integer,Int) -> Map.Map Int Integer ->
              [([ModuloCase], Map.Map Int Integer,[Map.Map Int Integer], [Map.Map Int Integer])]
            twinItems xPos yPos n (top,modIndex) bottom
              = (map (transformQuad (++ [findCase xPos yPos False]) (zipMap plus $ Map.map (*n) top) id
                  (++ [xEquation]
                   ++ [xLowerBound False]
                   ++ [xUpperBound False])) m)
                ++ (map (transformQuad (++ [findCase xPos yPos True]) (zipMap plus (Map.map (*n) top) . add' (modIndex, n)) id
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
                   ++ [add' (modIndex,if xPos then -1 else 1) (signEq (not yPos) bottom)])) m)
              where
                -- x >= 1 or x <= -1  (rearranged: -1 + x >= 0 or -1 - x >= 0)
                xEquation = add' (0,-1) (signEq xPos top)
                -- We include (x [+ a] >= 0 or x [+ a] <= 0) even though they are redundant in some cases (addA = False):
                xLowerBound addA = signEq xPos $ (if addA then add' (modIndex,1) else id) top
                -- We want to add the bounds as follows:
                -- xPos yPos | Equation
                -- T    T    | y - 1 - x - a  >= 0
                -- T    F    | -y - 1 - x - a >= 0
                -- F    T    | x + a - 1 + y  >= 0
                -- F    F    | x + a - y - 1  >= 0
                -- Therefore the sign of y in the equation is yPos, the sign of x and a is (not xPos)
                xUpperBound addA = add' (0,-1) $ zipMap plus (signEq (not xPos) ((if addA then add' (modIndex,1) else id) top)) (signEq yPos bottom)
                
                signEq sign eq = if sign then eq else Map.map negate eq
                
                findCase xPos yPos aNonZero = case (xPos, yPos, aNonZero) of
                  (True , True , True ) -> XPosYPosANonZero
                  (True , True , False) -> XPosYPosAZero
                  (True , False, True ) -> XPosYNegANonZero
                  (True , False, False) -> XPosYNegAZero
                  (False, True , True ) -> XNegYPosANonZero
                  (False, True , False) -> XNegYPosAZero
                  (False, False, True ) -> XNegYNegANonZero
                  (False, False, False) -> XNegYNegAZero
            
        makeEquation' m div@(Divide n top bottom)
          = do top' <- process (Set.toList top) >>* map (\(_,a,b,c) -> (a,b,c))
               top'' <- getSingleItem "Modulo or Divide not allowed in the numerator of Divide" top'
               bottom' <- process (Set.toList bottom) >>* map (\(_,a,b,c) -> (a,b,c))
               divIndex <- varIndex div
               case onlyConst (Set.toList bottom) of
                 Just bottomConst -> 
                   let add_m :: Map.Map Int Integer -> Map.Map Int Integer
                       add_m = zipMap plus (Map.fromList [(divIndex,n)])
                       add_x_minus_my = zipMap plus top'' . zipMap plus (Map.fromList [(divIndex,-bottomConst)]) in
                   return $
                     -- The zero option (x = 0, x REM y = 0):
                   ( map (transformQuad (++ [XZero]) id (++ [top'']) id) m)
                   ++
                     -- The top-is-positive option:
                   ( map (transformQuad (++ [XPos]) add_m id (++
                      -- x >= 1
                      [zipMap plus (Map.fromList [(0,-1)]) top''
                      -- m >= 0 if y positive
                      -- m <= 0 (i.e. -m >= 0) if y negative
                      ,Map.fromList [(divIndex, signum bottomConst)]
                      -- x + my + 1 - y <= 0 if y positive
                      -- x + my - 1 - y >= 0 if y negative
                      ,(if (bottomConst > 0) then Map.map negate else id) $ add_x_minus_my $ Map.fromList [(0,signum bottomConst - bottomConst)]
                      -- x + my >= 0 if y positive
                      -- x + my <= 0 if negative
                      ,(if (bottomConst > 0) then id else Map.map negate) $ add_x_minus_my $ Map.empty])
                     ) m) ++
                    -- The top-is-negative option:
                   ( map (transformQuad (++ [XNeg]) add_m id (++
                      -- x <= -1
                      [add' (0,-1) $ Map.map negate top''
                      -- m <= 0 if y positive
                      -- m >= 0 if y negative
                      ,Map.fromList [(divIndex, - signum bottomConst)]
                      -- x + my - 1 + y >= 0 if y positive
                      -- x + my + 1 + y <= 0 if y negative
                      ,(if (bottomConst > 0) then id else Map.map negate) $ add_x_minus_my $ Map.fromList [(0,bottomConst - signum bottomConst)]
                      -- x + my <= 0 if y positive
                      -- x + my >= 0 if y negative
                      ,(if (bottomConst > 0) then Map.map negate else id) $ add_x_minus_my Map.empty])
                     ) m)
                 _ -> throwError "Variables in divisor not supported by usage checker"
        
        empty :: [([ModuloCase],Map.Map Int Integer,[Map.Map Int Integer], [Map.Map Int Integer])]
        empty = [([],Map.empty,[],[])]
        
        plus :: Num n => Maybe n -> Maybe n -> Maybe n
        plus x y = Just $ (fromMaybe 0 x) + (fromMaybe 0 y)
        
        add' :: (Int,Integer) -> Map.Map Int Integer -> Map.Map Int Integer
        add' (m,n) = Map.insertWith (+) m n
        
        add :: (Int,Integer) -> [(z,Map.Map Int Integer,a,b)] -> [(z,Map.Map Int Integer,a,b)]
        add (m,n) = map $ (\(a,b,c,d) -> (a,(Map.insertWith (+) m n) b,c,d))
    
-- | Converts a map to an array.  Any missing elements in the middle of the bounds are given the value zero.
-- Could probably be moved to Utils
mapToArray :: (IArray a v, Num v, Num k, Ord k, Ix k) => Map.Map k v -> a k v
mapToArray m = accumArray (+) 0 (0, highest') . Map.assocs $ m
      where
        highest' = maximum $ 0 : Map.keys m

-- | Given a pair of equation sets, makes all the equations in the lists be the length
-- of the longest equation.  All missing elements are of course given value zero.
squareEquations :: ([Array CoeffIndex Integer],[Array CoeffIndex Integer]) -> ([Array CoeffIndex Integer],[Array CoeffIndex Integer])
squareEquations (eqs,ineqs) = uncurry transformPair (mkPair $ map $ makeArraySize (0,highest) 0) (eqs,ineqs)
    
      where      
        highest = maximum $ 0 : (concatMap indices $ eqs ++ ineqs)

