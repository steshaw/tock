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

module ImplicitMobility (implicitMobility, mobiliseArrays, inferDeref) where

import Control.Arrow
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Trans
import Data.Graph.Inductive
import Data.Graph.Inductive.Query.DFS
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Traversable as T

import qualified AST as A
import CompState
import Data.Generics.Alloy.Route
import Errors
import FlowAlgorithms
import FlowGraph
import FlowUtils
import Intrinsics
import Metadata
import Pass
import ShowCode
import Traversal
import Types
import UsageCheckUtils
import Utils

effectDecision :: Var -> Decision -> AlterAST PassM () -> A.AST -> PassM A.AST
effectDecision _ Move _ = return -- Move is the default
effectDecision targetVar (Copy _) (AlterProcess wrapper) = routeModify wrapper alterProc
  where
    alterProc :: A.Process -> PassM A.Process
    alterProc (A.Assign m lhs (A.ExpressionList m' [e]))
      = return $ A.Assign m lhs $ A.ExpressionList m' [A.CloneMobile m' e]
    alterProc (A.Output m cv [A.OutExpression m' e])
      = return $ A.Output m cv [A.OutExpression m' $ A.CloneMobile m' e]
    alterProc x = dieP (findMeta x) "Cannot alter process to copy"
effectDecision _ (Copy _) _ = return

-- | Calculates a map from each node to a set of variables that will be
-- used again afterwards.  Used in this context means it can possibly be
-- read from before being written to
calculateUsedAgainAfter :: Monad m => FlowGraph m UsageLabel -> Node -> Either String (Map.Map Node
 (Set.Set Var))
calculateUsedAgainAfter g startNode
  = flowAlgorithm funcs (rdfs [startNode] g) (startNode, Set.empty)
  where
    funcs :: GraphFuncs Node EdgeLabel (Set.Set Var)
    funcs = GF     
      { nodeFunc = iterate
      -- Backwards data flow:
      , nodesToProcess = lsuc g
      , nodesToReAdd = lpre g
      , defVal = Set.empty
      , userErrLabel = ("for node at: " ++) . show . fmap getNodeMeta . lab g
      }

    iterate :: (Node, EdgeLabel) -> Set.Set Var -> Maybe (Set.Set Var) -> Set.Set
      Var
    iterate node prevVars maybeVars = case lab g (fst node) of
      Just ul ->
        let vs = nodeVars $ getNodeData ul
            readFromVars = readVars vs
            writtenToVars = writtenVars vs
            addTo = fromMaybe prevVars maybeVars
        in (readFromVars `Set.union` addTo) `Set.difference` Map.keysSet writtenToVars
      Nothing -> error "Node label not found in calculateUsedAgainAfter"

type UsedParM = StateT (Set.Set Node) (Either ErrorReport)

instance Die UsedParM where
  dieReport = lift . dieReport

type NodeToVars = Map.Map Node (Map.Map Var Int)

--TODO prevent going round in circles forever!
calculateUsedInParallel :: Monad m => FlowGraph m UsageLabel -> [Node] -> Node -> Either
  ErrorReport NodeToVars
calculateUsedInParallel g roots startNode
  = flip evalStateT Set.empty $ liftM combine $ mapM proceedSeq (roots `intersect` rdfs [startNode] g)
  where
    combine :: [NodeToVars] -> NodeToVars
    combine = foldl (Map.unionWith (Map.unionWith (+))) Map.empty
    add :: NodeToVars -> NodeToVars -> NodeToVars
    add = Map.unionWith (Map.unionWith (+))

    isESeq :: EdgeLabel -> Bool
    isESeq (ESeq {}) = True
    isESeq _ = False

    nodeData :: Node -> Bool -> NodeToVars
    nodeData n rep = maybe Map.empty (Map.singleton n . flip setToMap x) $
      fmap (readVars . nodeVars . getNodeData) $ lab g n
      where
        x :: Int
        x = if rep then 2 else 1

    isRep :: Node -> Bool
    isRep = isJust . maybe Nothing nodeRep . fmap getNodeData . lab g

    proceedSeq :: Node -> UsedParM NodeToVars
    proceedSeq n
      = do been <- get
           modify (Set.insert n)
           if n `Set.member` been
             then return Map.empty
             else let myvs = nodeData n False in case nub $ map snd $ lsuc g n of
               [EStartPar i] -> do r <- mapM (proceedPar (i, isRep n)) (suc g n)
                                   let (ns, vs) = (catMaybes *** combine) $ unzip r
                                   liftM (add (add myvs vs) . combine) $ mapM proceedSeq ns
               es | all isESeq es -> liftM (add myvs . combine) $ mapM proceedSeq $ suc g n
               es -> dieP (getMetaSafe g n) $ "Unexpected edge types in proceedSeq: " ++ show es

    proceedPar :: (Integer, Bool) -> Node -> UsedParM (Maybe Node, NodeToVars)
    proceedPar (i, rep) n
      = do been <- get
           modify (Set.insert n)
           if n `Set.member` been
             then return (Nothing, Map.empty)
             else let myvs = nodeData n rep in case nub $ map snd $ lsuc g n of
               [EStartPar i'] -> do r <- mapM (proceedPar (i', isRep n)) (suc g n)
                                    let (ns, vs) = (catMaybes *** combine) $ unzip r
                                    case nub ns of
                                      [n'] -> liftM (second (add $ add myvs vs)) $ proceedPar (i, rep) n'
                                      _ -> dieP (getMetaSafe g n) "More than one node at end of par in proceedPar"
               [EEndPar i'] | i == i' ->  return (listToMaybe $ suc g n, myvs)
               es | all isESeq es -> do r <- mapM (proceedPar (i, rep)) $ suc g n
                                        let (ns, vs) = (catMaybes *** combine) $ unzip r
                                        case nub ns of
                                          [n'] -> return (Just n', add myvs vs)
                                          [] -> return (Nothing, add myvs vs)
                                          ns' -> dieP (getMetaSafe g n) $ "More than one node at end of par in proceedPar:"
                                            ++ show (map (getMetaSafe g) ns')
               _ -> dieP (getMetaSafe g n) $ "Unexpected edge types in proceedPar"

getMetaSafe :: Monad m => FlowGraph m UsageLabel -> Node -> Meta
getMetaSafe g = maybe emptyMeta getNodeMeta . lab g


--TODO rememember to take note of declarations/scope, otherwise this:
-- seqeach (..) {int:x; ... x = 3;}
-- will look like x is used again on the next loop iteration

-- TODO look at the types, too!
printMoveCopyDecisions :: Decisions -> PassM ()
printMoveCopyDecisions decs
  = mapM_ printDec $ Map.toList decs
  where
    printDec :: ((Node, Var), Decision) -> PassM ()
    printDec ((_,v), dec) = astTypeOf v >>= \t -> (liftIO $ putStrLn $
      show (findMeta v) ++ show v ++ " " ++ show t ++ " " ++ show dec)

data Decision = Move | Copy Meta deriving (Show, Ord, Eq)

makeMoveCopyDecisions :: forall m. Monad m => FlowGraph m UsageLabel -> [Node] -> [Node] ->
  PassM Decisions
makeMoveCopyDecisions grOrig roots ns
  = do namesWithTypes <- getCompState >>* csNames >>= T.mapM (typeOfSpec . A.ndSpecType)
       --liftIO $ putStrLn $ graphviz' $ nmap getNodeMeta grOrig
       let mobVars = Set.mapMonotonic (Var . A.Variable emptyMeta . A.Name emptyMeta)
                     . Map.keysSet
                     . Map.filter isJustMobileType
                     $ namesWithTypes
       foldM (processConnected $ nmap (fmap $ filterVars mobVars) grOrig) (Map.empty) ns
  where
    isJustMobileType :: Maybe A.Type -> Bool
    isJustMobileType (Just (A.Mobile {})) = True
    isJustMobileType _ = False
    
    filterVars :: Set.Set Var -> UsageLabel -> UsageLabel
    filterVars keep u
      = u { nodeVars = filterNodeVars (nodeVars u) }
      where
        keepM = Map.fromAscList $ flip zip (repeat ()) $ Set.toAscList keep

        filterNodeVars :: Vars -> Vars
        filterNodeVars vs
          = vs { readVars = readVars vs `Set.intersection` keep
               , writtenVars = writtenVars vs `Map.intersection` keepM
               , usedVars = readVars vs `Set.intersection` keep }
    
    -- Processes the entire sub-graph that is connected to the given node
    processConnected :: FlowGraph m UsageLabel -> Map.Map (Node, Var) Decision -> Node ->
      PassM (Map.Map (Node, Var) Decision)
    processConnected gr m n = case calculateUsedAgainAfter gr n of
      Left err -> dieP (getNodeMeta $ fromJust $ lab gr n) err
      Right mvs -> case calculateUsedInParallel gr roots n of
        Left err -> throwError err
        Right mp -> --liftIO $ putStrLn $ show mp
                    foldM (processNode gr mvs mp) m $ Map.keys mvs

    -- Processes all the variables at a given node
    processNode :: FlowGraph m UsageLabel -> Map.Map Node (Set.Set Var) ->
      NodeToVars
      -> Map.Map (Node, Var) Decision -> Node -> PassM (Map.Map (Node, Var) Decision)
    processNode gr mvs mp m n
      = case fmap (readVars . nodeVars . getNodeData) $ lab gr n of
          Nothing -> dieP emptyMeta "Did not find node label during implicit mobility"
          Just rvs -> return $ foldl (process n mvs mp) m $ Set.toList rvs

    -- Processes a single variable at a given node
    process :: Node -> Map.Map Node (Set.Set Var) -> NodeToVars -> Map.Map (Node, Var) Decision ->
      Var -> Map.Map (Node, Var) Decision
    process n useAgain usedInPar prev v = let s = Map.findWithDefault Set.empty n useAgain
                                              uvs = Map.findWithDefault Map.empty n usedInPar
                                              u = Map.findWithDefault 1 v uvs
      in Map.insert (n, v)
        (if v `Set.member` s
           then Copy $ findMeta $ Set.findMin $ Set.filter (== v) s
           else if u > 1
                  then Copy $ getMetaSafe grOrig n
                  else Move) prev

type Decisions = Map.Map (Node, Var) Decision

effectMoveCopyDecisions :: FlowGraph PassM UsageLabel -> Decisions -> A.AST -> PassM A.AST
effectMoveCopyDecisions g decs = foldFuncsM $ map effect $ Map.toList decs
  where
    effect :: ((Node, Var), Decision) -> A.AST -> PassM A.AST
    effect ((n, v), dec)
      = case fmap getNodeFunc $ lab g n of
          Nothing -> const $ dieP (findMeta v) "Could not find label for node"
          Just mod -> effectDecision v dec mod

implicitMobility :: Pass A.AST
implicitMobility 
  = pass "Implicit mobility optimisation"
    [] [] --TODO properties
   (passOnlyOnAST "implicitMobility" $ \t -> do
       g' <- buildFlowGraph labelUsageFunctions t
              :: PassM (Either String (FlowGraph' PassM UsageLabel (), [Node],
                [Node]))
       case g' of
         Left err -> dieP emptyMeta $ "Error building flow graph: " ++ err
         Right (g, roots, terms) ->
           -- We go from the terminator nodes, because we are performing backward
           -- data-flow analysis
           do decs <- makeMoveCopyDecisions g roots terms
              printMoveCopyDecisions decs
              effectMoveCopyDecisions g decs t)

mobiliseArrays :: PassASTOnStruct
mobiliseArrays = pass "Make all arrays mobile" [] [] recurse
  where
    ops :: ExtOpMSP BaseOpM
    ops = opMS (ops, doStructured)

    recurse :: RecurseM PassM (ExtOpMS BaseOpM)
    recurse = makeRecurseM ops
    descend :: DescendM PassM (ExtOpMS BaseOpM)
    descend = makeDescendM ops

    doStructured :: TransformStructured' (ExtOpMS BaseOpM)
    doStructured s@(A.Spec m (A.Specification m' n (A.Declaration m'' t@(A.Array ds
      innerT))) scope)
      = case innerT of
          A.Chan {} -> case mobiliseArrayInside (t, A.Declaration m'') of
            Just newSpec ->
              do modifyName n (\nd -> nd {A.ndSpecType = newSpec})
                 recurse scope >>* A.Spec m (A.Specification m' n newSpec)
            Nothing -> descend s
          A.ChanEnd {} -> case mobiliseArrayInside (t, A.Declaration m'') of
            Just newSpec ->
              do modifyName n (\nd -> nd {A.ndSpecType = newSpec})
                 recurse scope >>* A.Spec m (A.Specification m' n newSpec)
            Nothing -> descend s
          _ -> do scope' <- recurse {-addAtEndOfScopeDyn m'' (A.ClearMobile m'' $ A.Variable m' n)-} scope
                  let newSpec = A.Is m'' A.Original (A.Mobile t) $
                        A.ActualExpression $ A.AllocMobile m'' (A.Mobile t) Nothing
                  modifyName n (\nd -> nd {A.ndSpecType = newSpec})
                  return $ A.Spec m (A.Specification m' n newSpec) scope'

    doStructured (A.Spec m (A.Specification m' n (A.Proc m'' sm fs body)) scope)
      = do scope' <- recurse scope
           body' <- recurse body
           fs' <- mapM processFormal fs
           let newSpecF = A.Proc m'' sm fs'
           modifyName n (\nd -> nd {A.ndSpecType =
             let A.Proc _ _ _ stub = A.ndSpecType nd in newSpecF stub})
           return $ A.Spec m (A.Specification m' n (newSpecF body')) scope'

    doStructured (A.Spec m (A.Specification m' n (A.Protocol m'' ts)) scope)
      = do let ts' = [case t of
                        A.Array {} -> A.Mobile t
                        _ -> t
                     | t <- ts]
               newSpec = A.Protocol m'' ts'
           modifyName n (\nd -> nd {A.ndSpecType = newSpec})
           scope' <- recurse scope
           return $ A.Spec m (A.Specification m' n newSpec) scope'

    doStructured (A.Spec m (A.Specification m' n (A.ProtocolCase m'' nts)) scope)
      = do let nts' = [(n, [case t of
                         A.Array {} -> A.Mobile t
                         _ -> t
                      | t <- ts]) | (n, ts) <- nts]
               newSpec = A.ProtocolCase m'' nts'
           modifyName n (\nd -> nd {A.ndSpecType = newSpec})
           scope' <- recurse scope
           return $ A.Spec m (A.Specification m' n newSpec) scope'

    -- Must also mobilise channels of arrays, and arrays of channels of arrays:
    doStructured s@(A.Spec m (A.Specification m' n st) scope)
      = do mtf <- typeOfSpec' st
           case mtf >>= mobiliseArrayInside of
             Just newSpec ->
               do scope' <- recurse scope
                  modifyName n (\nd -> nd {A.ndSpecType = newSpec})
                  return $ A.Spec m (A.Specification m' n newSpec) scope'
             Nothing -> descend s

    doStructured s = descend s

    processFormal :: A.Formal -> PassM A.Formal
    processFormal f@(A.Formal am t n)
      = case mobiliseArrayInside (t, A.Declaration (A.nameMeta n)) of
          Just decl@(A.Declaration _ t') ->
            do modifyName n $ \nd -> nd {A.ndSpecType = decl}
               return $ A.Formal am t' n
          Nothing -> return f 

    mobiliseArrayInside :: (A.Type, A.Type -> A.SpecType) -> Maybe A.SpecType
    mobiliseArrayInside (A.Chan attr t@(A.Array {}), f)
      = Just $ f $ A.Chan attr $ A.Mobile t
    mobiliseArrayInside (A.ChanEnd attr dir t@(A.Array {}), f)
      = Just $ f $ A.ChanEnd attr dir $ A.Mobile t
    mobiliseArrayInside (A.Array ds (A.Chan attr t@(A.Array {})), f)
      = Just $ f $ A.Array ds $ A.Chan attr $ A.Mobile t
    mobiliseArrayInside (A.Array ds (A.ChanEnd attr dir t@(A.Array {})), f)
      = Just $ f $ A.Array ds $ A.ChanEnd attr dir $ A.Mobile t
    mobiliseArrayInside _ = Nothing

class Dereferenceable a where
  deref :: Meta -> a -> Maybe a

instance Dereferenceable A.Variable where
  deref m = Just . A.DerefVariable m

instance Dereferenceable A.Expression where
  deref m (A.ExprVariable m' v) = fmap (A.ExprVariable m') $ deref m v
  deref m (A.AllocMobile _ _ (Just e)) = Just e
  deref _ _ = Nothing

instance Dereferenceable A.Actual where
  deref m (A.ActualVariable v) = fmap A.ActualVariable $ deref m v
  deref m (A.ActualExpression e) = fmap A.ActualExpression $ deref m e

inferDeref :: PassOn2 A.Process A.Variable
inferDeref = pass "Infer mobile dereferences" [] [] recurse
  where
    ops = doProcess :-* doVariable :-* baseOpM

    recurse :: RecurseM PassM (TwoOpM A.Process A.Variable)
    recurse = makeRecurseM ops
    descend :: DescendM PassM (TwoOpM A.Process A.Variable)
    descend = makeDescendM ops

    unify :: (Dereferenceable a, ASTTypeable a, ShowOccam a, ShowRain a) => Meta
      -> A.Type -> a -> PassM a
    unify _ (A.Mobile t) x = return x
    unify m t x = do xt <- astTypeOf x
                     case xt of
                       A.Mobile {} -> case deref m x of
                         Just x' -> return x'
                         Nothing -> diePC m $ formatCode "Unable to dereference %" x
                       _ -> return x

    doProcess :: Transform A.Process
    doProcess (A.ProcCall m n as)
      = do as' <- recurse as
           A.Proc _ _ fs _ <- specTypeOfName n
           ts <- mapM astTypeOf fs
           as'' <- mapM (uncurry $ unify m) (zip ts as')
           return $ A.ProcCall m n as''
    doProcess (A.IntrinsicProcCall m n as)
      = do let Just amtns = lookup n intrinsicProcs
           as' <- mapM (uncurry $ unify m) (zip (map mid amtns) as)
           return $ A.IntrinsicProcCall m n as'
      where mid (_,y,_) = y
    doProcess p = descend p

    doVariable :: Transform A.Variable
    doVariable all@(A.SubscriptedVariable m sub v)
      = do t <- astTypeOf v
           case t of
             A.Mobile {} -> return $ A.SubscriptedVariable m sub $ fromJust (deref m v)
             _ -> descend all
    doVariable v = descend v
