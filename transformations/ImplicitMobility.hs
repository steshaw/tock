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

import Control.Monad
import Control.Monad.Trans
import Data.Generics
import Data.Graph.Inductive
import Data.Graph.Inductive.Query.DFS
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Traversable as T

import qualified AST as A
import CompState
import Errors
import FlowAlgorithms
import FlowGraph
import FlowUtils
import GenericUtils
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
    derefExp :: A.Expression -> PassM A.Expression
    derefExp e
      = do t <- astTypeOf e
           {-case t of
             A.Mobile (A.List _) -> return ()
             A.List _ -> return ()
             _ -> dieP (findMeta e) $
               "Cannot dereference a non-list assignment RHS: " ++ show t -}
           case e of
             A.ExprVariable m' v ->
               if (Var v == targetVar)
                 then return $ A.ExprVariable m' $ A.DerefVariable m' v
                 else return e
             -- TODO handle concat expressions with repeated vars
             A.Dyadic m A.Concat lhs rhs ->
               do lhs' <- derefExp lhs
                  rhs' <- derefExp rhs
                  return $ A.Dyadic m A.Concat lhs' rhs'
             _ -> return e
    alterProc :: A.Process -> PassM A.Process
    alterProc (A.Assign m lhs (A.ExpressionList m' [e]))
      = do e' <- derefExp e
           return $ A.Assign m lhs $ A.ExpressionList m' [e']
    alterProc (A.Output m cv [A.OutExpression m' e])
      = do e' <- derefExp e
           return $ A.Output m cv [A.OutExpression m' e']
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

makeMoveCopyDecisions :: forall m. Monad m => FlowGraph m UsageLabel -> [Node] ->
  PassM Decisions
makeMoveCopyDecisions grOrig ns
  = do namesWithTypes <- getCompState >>* csNames >>= T.mapM (typeOfSpec . A.ndSpecType)
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
      Right mvs -> foldM (processNode gr mvs) m $ Map.keys mvs

    -- Processes all the variables at a given node
    processNode :: FlowGraph m UsageLabel -> Map.Map Node (Set.Set Var) -> Map.Map (Node, Var) Decision
      -> Node -> PassM (Map.Map (Node, Var) Decision)
    processNode gr mvs m n
      = case fmap (readVars . nodeVars . getNodeData) $ lab gr n of
          Nothing -> dieP emptyMeta "Did not find node label during implicit mobility"
          Just rvs -> return $ foldl (process n mvs) m $ Set.toList rvs

    -- Processes a single variable at a given node
    process :: Node -> Map.Map Node (Set.Set Var) -> Map.Map (Node, Var) Decision ->
      Var -> Map.Map (Node, Var) Decision
    process n useAgain prev v = let s = Map.findWithDefault Set.empty n useAgain
      in Map.insert (n, v)
        (if v `Set.member` s
           then Copy $ findMeta $ Set.findMin $ Set.filter (== v) s
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

implicitMobility :: Pass
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
           do decs <- makeMoveCopyDecisions g terms
              printMoveCopyDecisions decs
              effectMoveCopyDecisions g decs t)

mobiliseArrays :: Pass
mobiliseArrays = pass "Make all arrays mobile" [] [] recurse
  where
    ops = baseOp `extOpS` doStructured
    recurse, descend :: Data t => Transform t
    recurse = makeRecurse ops
    descend = makeDescend ops

    doStructured :: Data t => Transform (A.Structured t)
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
                  let newSpec = A.IsExpr m'' A.Original (A.Mobile t) $ A.AllocMobile m'' (A.Mobile t) Nothing
                  modifyName n (\nd -> nd {A.ndSpecType = newSpec})
                  let name_sizes = n {A.nameName = A.nameName n ++ "_sizes"}
                      nd = A.NameDef {
                             A.ndMeta = m,
                             A.ndName = A.nameName name_sizes,
                             A.ndOrigName = A.nameName name_sizes,
                             A.ndSpecType = A.Declaration m $
                               A.Array [A.Dimension $ makeConstant m (length ds)]
                                 A.Int,
                             A.ndAbbrevMode = A.Original,
                             A.ndNameSource = A.NamePredefined,
                             A.ndPlacement = A.Unplaced
                             }
                  defineName name_sizes nd
                  return $ A.Spec m (A.Specification m' n newSpec) scope'

    doStructured (A.Spec m (A.Specification m' n (A.Proc m'' sm fs body)) scope)
      = do scope' <- recurse scope
           body' <- recurse body
           fs' <- mapM processFormal fs
           let newSpecF = A.Proc m'' sm fs'
           modifyName n (\nd -> nd {A.ndSpecType =
             let A.Proc _ _ _ stub = A.ndSpecType nd in newSpecF stub})
           return $ A.Spec m (A.Specification m' n (newSpecF body')) scope'


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

-- TODO I think I want to clone, not dereference

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

inferDeref :: Pass
inferDeref = pass "Infer mobile dereferences" [] [] recurse
  where
    ops = baseOp `extOp` doProcess `extOp` doVariable
    recurse, descend :: Data t => Transform t
    recurse = makeRecurse ops
    descend = makeDescend ops

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
      = do A.Proc _ _ fs _ <- specTypeOfName n
           ts <- mapM astTypeOf fs
           as' <- mapM (uncurry $ unify m) (zip ts as)
           return $ A.ProcCall m n as'
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
