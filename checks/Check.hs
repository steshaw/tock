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
import Data.Graph.Inductive
import Data.List hiding (union)
import qualified Data.Map as Map
import Data.Maybe
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
                      let g' = labelMapWithNodeId (addBK reach cons g) g
                      checkPar (nodeRep . snd)
                        (joinCheckParFunctions checkArrayUsage checkPlainVarUsage)
                        g'
                      checkParAssignUsage g' t
                      checkProcCallArgsUsage g' t
--                      mapM_ (checkInitVar (findMeta t) g) roots
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


addBK :: Map.Map Node (Map.Map Var (Set.Set (Maybe A.Expression))) ->
  Map.Map Node [A.Expression] -> FlowGraph PassM UsageLabel ->
  Node -> FNode PassM UsageLabel -> FNode PassM (BK, UsageLabel)
addBK mp mp2 g nid n = fmap ((,) $ followBK (map (keepDefined . Map.fromListWith (++)) $
  productN $ conBK ++ repBK ++ values)) n
  where
    keepDefined :: Map.Map Var a -> Map.Map Var a
    keepDefined m = Map.intersection m $ Map.fromList
      [(Var (A.Variable emptyMeta (A.Name emptyMeta n)), ()) | n <- getNodeNames n]
    
    nodeInQuestion :: Map.Map Var (Set.Set (Maybe A.Expression))
    nodeInQuestion = fromMaybe Map.empty $ Map.lookup nid mp

    consInQuestion :: [A.Expression]
    consInQuestion = fromMaybe [] $ Map.lookup nid mp2

    conInterMed :: [([Var], [BackgroundKnowledge])]
    conInterMed = map f consInQuestion
      where
        f :: A.Expression -> ([Var], [BackgroundKnowledge])
        f e = (map Var $ listify (const True) e, g e)

        g :: A.Expression -> [BackgroundKnowledge]
        g (A.Dyadic _ op lhs rhs)
          | op == A.And = g lhs ++ g rhs
          | op == A.Eq = [Equal lhs rhs]
          | op == A.LessEq = [LessThanOrEqual lhs rhs]
          | op == A.MoreEq = [LessThanOrEqual rhs lhs]
          | op == A.Less = [LessThanOrEqual (addOne lhs) rhs]
          | op == A.More = [LessThanOrEqual (addOne rhs) lhs]
          -- TODO add support for OR, and NOT-EQUAL
        g _ = []

    conBK :: [[(Var, [BackgroundKnowledge])]]
    conBK = [ [(v, concatMap snd $ filter (elem v . fst) conInterMed)]
            | v <- nub $ concatMap fst conInterMed]
    
    -- Each list (xs) in the whole thing (xss) relates to a different variable
    -- Each item in a list xs is a different possible constraint on that variable
    -- (effectively joined together by OR)
    -- The items in the list of BackgroundKnowledge are joined together with
    -- AND
    values :: [[(Var, [BackgroundKnowledge])]]
    values = [ [(Var v, maybeToList $ fmap (Equal $ A.ExprVariable (findMeta v)
      v) val)  | val <- Set.toList vals]
             | (Var v, vals) <- Map.toList nodeInQuestion]
    -- Add bk based on replicator bounds
    -- Search for the node containing the replicator definition,
    -- TODO Then use background knowledge related to any variables mentioned in
    -- the bounds *at that node* not at the current node-in-question

    repBK :: [[(Var, [BackgroundKnowledge])]]
    repBK = mapMaybe (fmap mkBK . nodeRep . getNodeData . snd) $ labNodes g
      where
        --TODO only really need consider the connected nodes...

        mkBK :: (A.Name, A.Replicator) -> [(Var, [BackgroundKnowledge])]
        mkBK (n, A.For _ low count _) = [(Var v, bk)]
          where
            m = A.nameMeta n
            v = A.Variable m n
            bk = [ RepBoundsIncl v low (subOne $ A.Dyadic m A.Add low count)]
    
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

checkPlainVarUsage :: forall m. (MonadIO m, Die m, CSMR m) => (Meta, ParItems (BK, UsageLabel)) -> m ()
checkPlainVarUsage (m, p) = check p
  where
    addBK :: BK -> Vars -> VarsBK
    addBK bk vs = VarsBK (Map.fromAscList $ zip (Set.toAscList $ readVars vs) (repeat bk))
                         ((Map.map (\me -> (maybeToList me, bk)) $ writtenVars vs)
                          `Map.union` Map.fromAscList (zip (Set.toAscList $ usedVars
                            vs) (repeat ([], bk))))

    reps (RepParItem r p) = r : reps p
    reps (SeqItems _) = []
    reps (ParItems ps) = concatMap reps ps

    getVars :: ParItems (BK, UsageLabel) -> Map.Map Var (Maybe BK, Maybe BK)
    getVars (SeqItems ss) = foldUnionVarsBK $ [addBK bk $ nodeVars u | (bk, u) <- ss]
    getVars (ParItems ps) = foldl (Map.unionWith join) Map.empty (map getVars ps)
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
      = do sharedNames <- getCompState >>* csNameAttr >>* Map.filter (== NameShared)
             >>* Map.keysSet >>* (Set.map $ UsageCheckUtils.Var . A.Variable emptyMeta . A.Name emptyMeta)
           let decl = concatMap getDecl ps
           filt <- filterPlain
           let examineVars =
                 map (filterMapByKey filt . (`difference` (Set.fromList decl `Set.union` sharedNames)))
                   (map getVars ps)
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
         return $ "{" ++ concat (intersperse ", " ss) ++ "}"

checkInitVarPass :: Pass
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
      = do checkPlainVarUsage (m, mockedupParItems)
           checkArrayUsage (m, mockedupParItems)
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
    checkArgs (p@(A.ProcCall m _ _), (bk, _))
      = do vars <- getVarProcCall p
           let mockedupParItems = fmap ((,) bk) $
                 ParItems [SeqItems [Usage Nothing Nothing Nothing v]
                          | v <- vars]
           checkPlainVarUsage (m, mockedupParItems)
           checkArrayUsage (m, mockedupParItems)

-- This isn't actually just unused variables, it's all unused names (except PROCs)
checkUnusedVar :: CheckOptM ()
checkUnusedVar = forAnyASTStructBottomUpAccum doSpec
  where
    doSpec :: Data a => A.Structured a -> CheckOptASTM' [A.Name] (A.Structured a) ()
     -- Don't touch PROCs, for now:
    doSpec (A.Spec _ (A.Specification mspec name (A.Proc {})) scope) = return ()
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
                   substitute scope
    doSpec _ = return ()
