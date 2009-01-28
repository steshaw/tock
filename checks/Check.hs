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

-- | This code implements various usage checking.  It is designed to work with
-- the control-flow graph stuff, hence the use of functions that match the dictionary
-- of functions in FlowGraph.  This is also why we don't drill down into processes;
-- the control-flow graph means that we only need to concentrate on each node that isn't nested.
module Check (checkInitVarPass, usageCheckPass, checkUnusedVar) where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans
import Data.Generics
import Data.Graph.Inductive hiding (mapSnd)
import Data.List hiding (union)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set

import ArrayUsageCheck
import qualified AST as A
import CheckFramework
import CompState
import Errors
import ExSet
import FlowAlgorithms
import FlowGraph
import FlowUtils
import GenericUtils
import Metadata
import Pass
import ShowCode
import Traversal
import Types
import UsageCheckAlgorithms
import UsageCheckUtils
import Utils

usageCheckPass :: A.AST -> PassM A.AST
usageCheckPass t = do g' <- buildFlowGraph labelUsageFunctions t
                      (g, roots) <- case g' of
                        Left err -> dieP (findMeta t) err
                        Right (g,rs,_) -> return (g,rs)
                      debug "Analysing flow graph"
                      reach <- case mapM (findReachDef g) roots >>* foldl Map.union
                        Map.empty of
                          Left err -> dieP emptyMeta $ "findReachDef: " ++
                            err
                          Right r -> return r
                      cons <- case mapM (findConstraints g) roots
                                     >>* foldl Map.union Map.empty of
                                Left err -> dieP emptyMeta $ "findConstraints:"
                                  ++ err
                                Right c -> return c
                      g' <- labelMapWithNodeIdM (addBK reach cons g) g
                      debug "Checking flow graph for problems"
                      checkPar (nodeRep . snd)
                        (joinCheckParFunctions
                          (checkArrayUsage NameShared)
                          (checkPlainVarUsage NameShared))
                        g'
                      debug "Checking parallel assignments"
                      checkParAssignUsage g' t
                      debug "Checking PROC arguments"
                      checkProcCallArgsUsage g' t
--                      mapM_ (checkInitVar (findMeta t) g) roots
                      debug "Completed usage checking"
                      return t

-- | For each entry in the BK, finds all the variables involved in a given piece
-- of BK and adds the BK from all other variables.  For example, let's say that
-- the BK for variable x is "x = y".  This function will add, under the key of
-- x, the BK from variable y, which might be say, "y <= z + 1", at which point
-- it will add the BK for z to the entry for x and so on.
followBK :: BK -> BK
followBK = map followBK'
  where
    followBK' :: Map.Map Var [BackgroundKnowledge] -> Map.Map Var [BackgroundKnowledge]
    followBK' m = Map.mapWithKey addAll m
      where
        addAll :: Var -> [BackgroundKnowledge] -> [BackgroundKnowledge]
        addAll v = addAll' (Set.singleton v)

        addAll' :: Set.Set Var -> [BackgroundKnowledge] -> [BackgroundKnowledge]
        addAll' prev bk
          | Set.null (next `Set.difference` prev) = bk
          | otherwise = bk ++ addAll' (next `Set.union` prev)
                          (concat $ mapMaybe (flip Map.lookup m) (Set.toList $
                            next `Set.difference` prev))
          where
            next = Set.fromList $ map Var $ listify (const True :: A.Variable -> Bool) bk


data And a = And [a]
data Or a = Or [a]

instance Monoid (And a) where
  mempty = And []
  mappend (And a) (And b) = And (a ++ b)
instance Monoid (Or a) where
  mempty = Or []
  mappend (Or a) (Or b) = Or (a ++ b)

instance Functor And where
  fmap f (And xs) = And $ map f xs

instance Functor Or where
  fmap f (Or xs) = Or $ map f xs

deAnd :: And a -> [a]
deAnd (And xs) = xs

deOr :: Or a -> [a]
deOr (Or xs) = xs

noOr :: a -> Or a
noOr = Or . singleton

noAnd :: a -> And a
noAnd = And . singleton


addBK :: Map.Map Node (Map.Map Var (Set.Set (Maybe A.Expression))) ->
  Map.Map Node [A.Expression] -> FlowGraph PassM UsageLabel ->
  Node -> FNode PassM UsageLabel -> PassM (FNode PassM (BK, UsageLabel))
addBK mp mp2 g nid n
  = do im <- conInterMed
       return $ fmap ((,) $ followBK (map keepDefined (joined' im))) n
  where
    keepDefined :: Map.Map Var a -> Map.Map Var a
    keepDefined m = Map.intersection m $ Map.fromList
      [(Var (A.Variable emptyMeta (A.Name emptyMeta n)), ()) | n <- getNodeNames n]
    
    nodeInQuestion :: Map.Map Var (Set.Set (Maybe A.Expression))
    nodeInQuestion = fromMaybe Map.empty $ Map.lookup nid mp

    consInQuestion :: And A.Expression
    consInQuestion = And $ fromMaybe [] $ Map.lookup nid mp2

    conInterMed :: PassM (And (Or BackgroundKnowledge))
    conInterMed = liftM mconcat $ mapM g $ deAnd consInQuestion
      where
        g :: A.Expression -> PassM (And (Or BackgroundKnowledge))
        g (A.FunctionCall m fn [lhs, rhs])
          -- If one of the components of an AND is unrecognised, we still keep
          -- the other part:
          | fn == bop "AND" = liftM2 mappend (g lhs) (g rhs)
          -- (A and B) or (C and D) = ((A and B) or C) and ((A and B) or D)
          -- = (A or C) and (B or C) and (A or D) and (B or D)
          --
          -- If one component of an OR is unrecognised, we end up dropping both
          -- halves because we can no longer count on that BK (given A OR B, where
          -- we recognise A, since we can't tell if B is true, we actually have
          -- no information about A even if the branch is taken).  We do know that
          -- if the branch is not taken, A cannot be true, but that's dealt with
          -- because a negated OR ends up as an AND, see above.
          | fn == bop "OR" = let f = liftM deAnd . g in
              do lhs' <- g lhs >>* deAnd
                 rhs' <- g rhs >>* deAnd
                 return $ And $ map (\(x,y) -> x `mappend` y) $ product2 (lhs', rhs')
          | otherwise
             = do mOp <- builtInOperator fn
                  case mOp of
                    Nothing -> return mempty
                    Just op ->
                      let noAndOr :: PassM a -> PassM (And (Or a))
                          noAndOr = liftM (noAnd . noOr)
                      in case op of
                          "=" -> noAndOr $ return $ Equal lhs rhs
                          "<=" -> noAndOr $ return $ LessThanOrEqual lhs rhs
                          ">=" -> noAndOr $ return $ LessThanOrEqual rhs lhs
                          "<" -> noAndOr $ do lhs_p1 <- addOne lhs
                                              return $ LessThanOrEqual lhs_p1 rhs
                          ">" -> noAndOr $ do rhs_p1 <- addOne rhs
                                              return $ LessThanOrEqual rhs_p1 lhs
                          "<>" -> liftM noAnd $ do
                             lhs_p1 <- addOne lhs
                             rhs_p1 <- addOne rhs
                             return $ Or [LessThanOrEqual lhs_p1 rhs
                                         ,LessThanOrEqual rhs_p1 lhs]
                          _ -> return mempty
          where
            bop n = A.Name emptyMeta $ occamDefaultOperator n [A.Bool, A.Bool]
        g (A.FunctionCall _ fn [rhs])
          | A.nameName fn == occamDefaultOperator "NOT" [A.Bool]
          = g $ negateExpr rhs
          where
            -- It is much easier (and clearer) to do the negation in the AST rather
            -- than play around with De Morgan's laws and so on to figure out how
            -- to invert the conjunction of disjunctions
            negateExpr (A.FunctionCall _ fn [rhs])
              | A.nameName fn == occamDefaultOperator "NOT" [A.Bool]
              = rhs
            negateExpr e@(A.FunctionCall m fn [lhs, rhs])
              | fn == bop "AND" = A.FunctionCall m (bop "OR") [negateExpr lhs, negateExpr rhs]
              | fn == bop "OR"  = A.FunctionCall m (bop "AND") [negateExpr lhs, negateExpr rhs]
              | otherwise =
                let pairs = [("<>", "=")
                            ,("<=", ">")
                            ,(">=", "<")]
                    rev (a, b) = [(bop a, bop b), (bop b, bop a)]
                    revOp = concatMap rev pairs
                in case lookup fn revOp of
                     Just op' -> A.FunctionCall m op' [lhs, rhs]
                     Nothing -> e -- Leave as is, because it won't be used anyway
              where
                bop n = A.Name emptyMeta $ occamDefaultOperator n [A.Bool, A.Bool]
            negateExpr e = e -- As above, leave as is

        g _ =  return mempty

    values :: And (Var, Or BackgroundKnowledge)
    values = And [
               (Var v, Or $ catMaybes [fmap (Equal $ A.ExprVariable (findMeta v) v) val
                          | val <- Set.toList vals])
             | (Var v, vals) <- Map.toList nodeInQuestion]
    -- Add bk based on replicator bounds
    -- Search for the node containing the replicator definition,
    -- TODO Then use background knowledge related to any variables mentioned in
    -- the bounds *at that node* not at the current node-in-question

    repBK :: And (Var, BackgroundKnowledge)
    repBK = And . mapMaybe (fmap mkBK . nodeRep . getNodeData . snd) $ labNodes g
      where
        --TODO only really need consider the connected nodes...

        mkBK :: (A.Name, A.Replicator) -> (Var, BackgroundKnowledge)
        mkBK (n, A.For _ low count _) = (Var v, bk)
          where
            m = A.nameMeta n
            v = A.Variable m n
            bk = RepBoundsIncl v low (subOneInt $ addExprsInt low count)

    -- How to join:
    -- repBK is just anded stuff, so we join that on to every conjunction in that
    -- variable.  values and constraints are And/Or, so we need to do some work to turn it into
    -- Or/And, and combine the two in a cartesian-product-like operation.
    joined :: And (Or BackgroundKnowledge) -> Or (Map.Map Var (And BackgroundKnowledge))
    joined interMed = Or
       [ possVal `union` makeMap possCon `union` (Map.map noAnd $ Map.fromList (deAnd repBK))
       | possVal <- makeNonEmpty Map.empty $ deOr convValues
       , possCon <- makeNonEmpty (And []) $ deOr convCon
       ]
      where
        union :: Map.Map Var (And BackgroundKnowledge) -> Map.Map Var (And BackgroundKnowledge)
          -> Map.Map Var (And BackgroundKnowledge)
        union = Map.unionWith mappend

        makeNonEmpty :: a -> [a] -> [a]
        makeNonEmpty x [] = [x]
        makeNonEmpty _ xs = xs
        
        makeMap :: And BackgroundKnowledge -> Map.Map Var (And BackgroundKnowledge)
        makeMap (And bks) = Map.fromListWith mappend $ concat
          [zip (map Var $ listify (const True) bk) (repeat $ noAnd bk) | bk <- bks]
        
        convValues :: Or (Map.Map Var (And BackgroundKnowledge))
        convValues = Or $ map (Map.fromListWith mappend) $
          map (mapSnd noAnd) $
          productN $ map (\(x, y) -> zip (repeat x) (deOr y)) $ deAnd values

        convCon :: Or (And BackgroundKnowledge)
        convCon = Or $ map And $ productN $ map deOr $ deAnd interMed

    joined' :: And (Or BackgroundKnowledge) -> BK
    joined' interMed = map (Map.map deAnd) $ deOr (joined interMed)

-- filter out array accesses, leave everything else in:
filterPlain :: CSMR m => m (Var -> Bool)
filterPlain = return isPlain
  where
    isPlain (Var (A.SubscriptedVariable _ (A.SubscriptField {}) v)) = isPlain (Var v)
    isPlain (Var (A.SubscriptedVariable {})) = False
    isPlain _ = True

filterPlain' :: CSMR m => ExSet Var -> m (ExSet Var)
filterPlain' Everything = return Everything
filterPlain' (NormalSet s) = filterPlain >>* flip Set.filter s >>* NormalSet

data VarsBK = VarsBK {
  readVarsBK :: Map.Map Var BK
  ,writtenVarsBK :: Map.Map Var ([A.Expression], BK)
}

-- | Unions all the maps into one, with possible BK for read, and possible BK for written.
-- Since BK is a list which is a disjunction of things, we concatenate the BK for
-- different things, because a variable access under conditions A, as well as a
-- variable access under conditions B, is equivalent to a variable access in which
-- condition A or condition B holds.
foldUnionVarsBK :: [VarsBK] -> Map.Map Var (Maybe BK, Maybe BK)
foldUnionVarsBK
  -- unionWith, unlike intersectionWith, requires the same value type
  -- for both maps in the union, so we must convert then join:
  = foldl (Map.unionWith concatPair') Map.empty . map convert
  where
    joinPair (Just a, Nothing) (Nothing, Just b) = (Just a, Just b)

    concatPair' (a,b) (c,d) = (join a c, join b d)
      where
        join Nothing Nothing = Nothing
        join (Just a) Nothing = Just a
        join Nothing (Just a) = Just a
        join (Just a) (Just b) = Just (a++b)


    convert :: VarsBK -> Map.Map Var (Maybe BK, Maybe BK)
    convert (VarsBK r w) = Map.unionWith joinPair (Map.map mkR r) (Map.map mkW w)

    mkR bk = (Just bk, Nothing)
    mkW (_, bk) = (Nothing, Just bk)

checkPlainVarUsage :: forall m. (MonadIO m, Die m, CSMR m) => NameAttr -> (Meta, ParItems (BK, UsageLabel)) -> m ()
checkPlainVarUsage sharedAttr (m, p) = check p
  where
    addBK :: BK -> Vars -> m VarsBK
    addBK bk vs
      = do let read = Map.fromAscList $ zip (Set.toAscList $ readVars vs) (repeat bk)
           splitUsed <- splitEnds' $ Set.toList $ usedVars vs
           splitWritten <- concatMapM splitEnds (Map.toList $ writtenVars vs) >>* Map.fromList
           let used = Map.fromList (zip splitUsed (repeat ([], bk)))
           return $ VarsBK read
                      ((Map.map (\me -> (maybeToList me, bk)) splitWritten)
                         `Map.union` used)

    splitEnds' = liftM (map fst) . concatMapM splitEnds . flip zip (repeat ())

    splitEnds :: (Var, a) -> m [(Var, a)]
    splitEnds (Var v, x)
      = do t <- astTypeOf v
           case (t, v) of
             -- Push the direction up to the array, not outside:
             (A.Chan {}, A.SubscriptedVariable m sub v')
               -> return [(Var $ A.SubscriptedVariable m sub $
                            A.DirectedVariable m dir v', x)
                         | dir <- [A.DirInput, A.DirOutput]]
             (A.Chan {}, _) -> return
               [(Var $ A.DirectedVariable (findMeta v) dir v, x)
               | dir <- [A.DirInput, A.DirOutput]]
             _ -> return [(Var v, x)]

    reps (RepParItem r p) = r : reps p
    reps (SeqItems _) = []
    reps (ParItems ps) = concatMap reps ps

    getVars :: ParItems (BK, UsageLabel) -> m (Map.Map Var (Maybe BK, Maybe BK))
    getVars (SeqItems ss) = liftM foldUnionVarsBK $ sequence [addBK bk $ nodeVars u | (bk, u) <- ss]
    getVars (ParItems ps) = liftM (foldl (Map.unionWith join) Map.empty) (mapM getVars ps)
      where
        join a b = (f (fst a) (fst b), f (snd a) (snd b))
        f Nothing x = x
        f x Nothing = x
        f (Just x) (Just y) = Just (x ++ y)

    getVars (RepParItem _ p) = getVars p

    getDecl :: ParItems (BK, UsageLabel) -> [Var]
    getDecl (ParItems ps) = concatMap getDecl ps
    getDecl (RepParItem _ p) = getDecl p
    getDecl (SeqItems ss) = mapMaybe
      (fmap (Var . A.Variable emptyMeta . A.Name emptyMeta) . join . fmap getScopeIn . nodeDecl
        . snd) ss
      where
        getScopeIn (ScopeIn _ n) = Just n
        getScopeIn _ = Nothing

    -- Check does not have to descend, because the overall checkPlainVarUsage function
    -- will be called on every single PAR in the whole tree
    check :: ParItems (BK, UsageLabel) -> m ()
    check (SeqItems {}) = return ()
    check (RepParItem _ p) = check (ParItems [p,p]) -- Easy way to check two replicated branches
    -- We first need to ignore all names that are shared, or declared inside the
    -- PAR that we are currently checking.  After that, we need to find all the
    -- variables written to in two of the maps in a list, and all the variables
    -- written to in one of the maps and read in another.  So we can find, for
    -- all the variables written in a map, whether it is read in any other.
    --
    -- A quick way to do this is to do a fold-union across all the maps, turning
    -- the values into lists that can then be scanned for any problems.
    check (ParItems ps)
      = do rawSharedNames <- getCompState >>* csNameAttr >>* Map.filter (Set.member sharedAttr)
             >>* Map.keysSet
           -- We add in the directed versions of each (channel or not) so that
           -- we make sure to ignore c? when c is shared:
           let allSharedNames
                 = Set.fromList $ concatMap (map UsageCheckUtils.Var .
                    flip applyAll [id, A.DirectedVariable emptyMeta A.DirInput
                                     , A.DirectedVariable emptyMeta A.DirOutput]
                    . A.Variable emptyMeta . A.Name emptyMeta) $ Set.toList rawSharedNames
           let decl = concatMap getDecl ps
           filt <- filterPlain
           vars <- mapM getVars ps
           let examineVars =
                 map (filterMapByKey filt . (`difference` (Set.fromList decl `Set.union` allSharedNames)))
                   vars
           checkCREW examineVars
      where
        difference m s = m `Map.difference` (Map.fromAscList $ zip (Set.toAscList
          s) (repeat ()))

    -- We must compare each read against all writes after us in the list,
    -- and each write against all reads and writes after us in the list:
    checkCREW :: [Map.Map Var (Maybe BK, Maybe BK)] -> m ()
    checkCREW [] = return ()
    checkCREW (m:ms) = do let folded = foldl (Map.unionWith concatPair) Map.empty $
                                map (Map.map (transformPair maybeToList maybeToList)) ms

                              reads = Map.map (fromJust . fst) $ Map.filter (isJust . fst) m
                              writes = Map.map (fromJust . snd) $ Map.filter (isJust . snd) m
                          sequence_ [checkBKReps msg v bk bks
                                    | (v, (bk, bks)) <- Map.toList $ Map.intersectionWith (,)
                                      reads (Map.map snd folded)]
                          sequence_ [checkBKReps msg v bk (bks++bks')
                                    | (v, (bk, (bks, bks'))) <- Map.toList $ Map.intersectionWith (,)
                                      writes folded]
                          checkCREW ms
      where
        msg = "The following variables are written and (written-to/read-from) inside a PAR: % when: "
    checkBKReps :: String -> Var -> BK -> [BK] -> m ()
    checkBKReps _ _ _ [] = return ()
    checkBKReps msg v bk bks
      = do sol <- if null (reps p)
                     -- If there are no replicators, it's definitely dangerous:
                     then return $ Just "<always>"
                     else findRepSolutions (reps p) (bk:bks)
           case sol of
             Nothing -> return ()
             Just sol' -> diePC m $ formatCode (msg ++ sol') v

showCodeExSet :: (CSMR m, Ord a, ShowOccam a, ShowRain a) => ExSet a -> m String
showCodeExSet Everything = return "<all-vars>"
showCodeExSet (NormalSet s)
    = do ss <- mapM showCode (Set.toList s)
         return $ "{" ++ joinWith ", " ss ++ "}"

checkInitVarPass :: Pass A.AST
checkInitVarPass = pass "checkInitVar" [] []
  (passOnlyOnAST "checkInitVar" $ runChecks checkInitVar)

-- | Checks that no variable is used uninitialised.  That is, it checks that every variable is written to before it is read.
checkInitVar :: CheckOptM ()
checkInitVar = forAnyFlowNode
  (\(g, roots, _) -> sequence
     [case flowAlgorithm (graphFuncs g) (dfs [r] g) (r, writeNode (fromJust $ lab g r)) of
       Left err -> dieP emptyMeta err
       Right x -> return x
     | r <- roots] >>* foldl Map.union Map.empty)
  checkInitVar'
       -- We check that for every variable read in each node, it has already been written to by then
  where
    -- Gets all variables read-from in a particular node, and the node identifier
    readNode :: UsageLabel -> ExSet Var
    readNode u = NormalSet $ readVars $ nodeVars u
  
    -- Gets all variables written-to in a particular node
    writeNode :: Monad m => FNode m UsageLabel -> ExSet Var
    writeNode nd = NormalSet $ Map.keysSet $ writtenVars $ nodeVars $ getNodeData nd
    
    -- Nothing is treated as if were the set of all possible variables:
    nodeFunction :: Monad m => FlowGraph m UsageLabel -> (Node, EdgeLabel) -> ExSet Var -> Maybe (ExSet Var) -> ExSet Var
    nodeFunction graph (n,_) inputVal Nothing = union inputVal (maybe emptySet writeNode (lab graph n))    
    nodeFunction graph (n, EEndPar _) inputVal (Just prevAgg) = unions [inputVal,prevAgg,maybe emptySet writeNode (lab graph n)]
    nodeFunction graph (n, _) inputVal (Just prevAgg) = intersection prevAgg $ union inputVal (maybe emptySet writeNode (lab graph n))
  
    graphFuncs :: Monad m => FlowGraph m UsageLabel -> GraphFuncs Node EdgeLabel (ExSet Var)
    graphFuncs graph = GF
      {
       nodeFunc = nodeFunction graph
       ,nodesToProcess = lpre graph
       ,nodesToReAdd = lsuc graph
       ,defVal = Everything
       ,userErrLabel = ("for node at: " ++) . show . fmap getNodeMeta . lab graph
      }
      
    checkInitVar' :: CheckOptFlowM (ExSet Var) ()
    checkInitVar'
      = do (v, vs) <- getFlowLabel >>* transformPair readNode (fromMaybe emptySet)
           filtv <- filterPlain' v
           filtvs <- filterPlain' vs
        -- The read-from set should be a subset of the written-to set:
           if filtv `isSubsetOf` filtvs then return () else 
             do vars <- showCodeExSet $ filtv `difference` filtvs
                m <- getFlowMeta
                warnP m WarnUninitialisedVariable $ "Variable(s) read from are not written to before-hand: " ++ vars

findAllProcess :: forall t m a. (Data t, Monad m) =>
  (A.Process -> Bool) -> FlowGraph' m a t -> A.Structured t -> [(A.Process, a)]
findAllProcess f g t = filter (f . fst) $ mapMaybe getProcess $ map snd $ labNodes g
  where
    getProcess :: FNode' t m a -> Maybe (A.Process, a)
    getProcess n = case getNodeFunc n of
      AlterProcess f -> Just (routeGet f t, getNodeData n)
      _ -> Nothing

checkParAssignUsage :: forall m t. (CSMR m, Die m, MonadIO m, Data t) =>
  FlowGraph' m (BK, UsageLabel) t -> A.Structured t -> m ()
checkParAssignUsage g = mapM_ checkParAssign . findAllProcess isParAssign g
  where
    isParAssign :: A.Process -> Bool
    isParAssign (A.Assign _ vs _) = length vs >= 2
    isParAssign _ = False

    -- | Need to check that all the destinations in a parallel assignment
    -- are distinct.  So we check plain variables, and array variables
    checkParAssign :: (A.Process, (BK, UsageLabel)) -> m ()
    checkParAssign (A.Assign m vs _, (bk, _))
      = do checkPlainVarUsage NameShared (m, mockedupParItems)
           checkArrayUsage NameShared (m, mockedupParItems)
      where
        mockedupParItems :: ParItems (BK, UsageLabel)
        mockedupParItems = fmap ((,) bk) $ ParItems [SeqItems [Usage Nothing Nothing Nothing
          $ processVarW v Nothing] | v <- vs]

checkProcCallArgsUsage :: forall m t. (CSMR m, Die m, MonadIO m, Data t) =>
  FlowGraph' m (BK, UsageLabel) t -> A.Structured t -> m ()
checkProcCallArgsUsage g = mapM_ checkArgs . findAllProcess isProcCall g
  where
    isProcCall :: A.Process -> Bool
    isProcCall (A.ProcCall {}) = True
    isProcCall _ = False

    -- | Need to check that all the destinations in a parallel assignment
    -- are distinct.  So we check plain variables, and array variables
    checkArgs :: (A.Process, (BK, UsageLabel)) -> m ()
    checkArgs (A.ProcCall _ _ [_], _) = return ()
    checkArgs (p@(A.ProcCall m _ _), (bk, _))
      = do debug $ "Checking PROC call at " ++ show m
           vars <- getVarProcCall p
           let mockedupParItems = fmap ((,) bk) $
                 ParItems [SeqItems [Usage Nothing Nothing Nothing v]
                          | v <- vars]
           checkPlainVarUsage NameAliasesPermitted (m, mockedupParItems)
           checkArrayUsage NameAliasesPermitted (m, mockedupParItems)
           debug $ "Done checking PROC call"

-- This isn't actually just unused variables, it's all unused names (except PROCs)
checkUnusedVar :: CheckOptM ()
checkUnusedVar = forAnyASTStructBottomUpAccum doSpec
  where
    doSpec :: Data a => A.Structured a -> CheckOptASTM' [A.Name] (A.Structured a) ()
     -- Don't touch PROCs, for now:
    doSpec (A.Spec _ (A.Specification mspec name (A.Proc {})) scope) = return ()
     -- Don't remove data types, in case the backend wants them:
    doSpec (A.Spec _ (A.Specification _ _ (A.DataType {})) _) = return ()
     -- DO NOT remove unused replicators!
    doSpec (A.Spec _ (A.Specification mspec name (A.Rep {})) scope) = return ()      
    doSpec (A.Spec _ (A.Specification mspec name _) scope)
      = do -- We can't remove _sizes arrays because the backend uses them for bounds
           -- checks that are not explicit in the AST.  We'll have to move the
           -- bounds checking forward into the AST before we can remove them.
           -- Making this more general, we don't actually remove any unused nonces.
           nd <- lookupName name
           when (A.ndNameSource nd == A.NameUser) $
            do usedNames <- askAccum >>* delete name
               -- ^ strip off one use of each name, since it's used in the spec
               when (not $ A.nameName name `elem` map A.nameName usedNames) $
                do warnPC mspec WarnUnusedVariable $ formatCode "Unused variable: %" name
                   modify (\st -> st { csNames = Map.delete (A.nameName name) (csNames st) })
                   -- substitute scope
    doSpec _ = return ()
