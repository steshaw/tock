{-
Tock: a compiler for parallel languages
Copyright (C) 2008  University of Kent

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

module CheckFramework (CheckOptM, CheckOptM', forAnyAST, forAnyASTStruct, substitute, restartForAnyAST,
  runChecks, runChecksPass, getFlowGraph, withChild, varsTouchedAfter,
  getCachedAnalysis, getCachedAnalysis') where

import Control.Monad.Reader
import Control.Monad.State
import Data.Generics
import Data.Graph.Inductive hiding (apply)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import GHC.Base (unsafeCoerce#)

import qualified AST as A
import CompState
import Errors
import FlowAlgorithms
import FlowGraph
import FlowUtils
import GenericUtils
import Metadata
import Pass
import Traversal
import UsageCheckUtils
import Utils

-- Temp:
todo = error "TODO"

-- Each data analysis only works on a connected sub-graph.  For forward data flow
-- this begins at the root node (the one with no predecessors, and thus is the
-- direct or indirect predecessor of all nodes it is connected to), for backwards
-- data flow it begins at the terminal node (the one with no successors, and thus
-- is the direct or indirect successor of all nodes it is connected to).
--
-- Each node has a unique corresponding root (the start of the PROC/FUNCTION) and
-- similarly a unique corresponding terminal (the end of the PROC/FUNCTION).  This
-- should be guaranteed by the building of the flow graph.
--
-- Each analysis gives back a map from nodes to some sort of label-value (dependent
-- on the analysis).  This map is calculated for a given connected sub-graph.
-- If the node you are looking for appears in the connected sub-graph (the keys
-- of the map), you use that map.  Since the analyses are run before unnesting
-- takes place, it is possible to descend down the AST into a inner PROC (a different
-- sub-graph) and then back up into the outer PROC.
--
-- To prevent re-running the analysis several times where there is no need, we
-- do the following:
--
-- * Modifying any node invalidates the flow-graph.  We currently calculate
-- the flow-graph for the whole AST at once, but I can't see an easy way to avoid
-- that (a more efficient way would be to just calculate the current connected
-- sub-graph) -- perhaps we could start from the part of the AST corresponding
-- to the root node?  TODO should be possible by using the route to the root node
-- of the current graph
--
-- * Modifying a node (e.g. with substitute or replaceBelow) invalidates all analyses.
-- 
-- I did have an idea that we could invalidate only analyses that contain
-- nodes that have a route that is prefixed by that of the current node.  So
-- for example, if you modify a node with route [1,3,1], we would find all
-- nodes with routes that match (1:3:1:_) and invalidate all currently held
-- analysis results containing any of those nodes.  This would help if for
-- example you do a substitute in an inner PROC, we do not have to invalidate
-- the analysis for the outer PROC.  But this idea DOES NOT WORK because the nodes
-- will change when the flow-graph is rebuilt, so we can't let the results get
-- out of sync with the flow-graph.  Unless in future we decouple the node identifiers
-- from our use of them a bit more (but remember not to use routes, as they are
-- not unique in the flow graph).


data CheckOptData = CheckOptData
 { ast :: A.AST
 , parItems :: Maybe (ParItems ())

 , nextVarsTouched :: Map.Map Node (Set.Set Var)

 , flowGraphRootsTerms :: Maybe (FlowGraph CheckOptM UsageLabel, [Node], [Node])

 , lastValidMeta :: Meta
 }

data FlowGraphAnalysis res = FlowGraphAnalysis
  { getFlowGraphAnalysis :: CheckOptData -> Map.Map Node res
  , addFlowGraphAnalysis :: Map.Map Node res -> CheckOptData -> CheckOptData
  , doFlowGraphAnalysis :: (FlowGraph CheckOptM UsageLabel, Node) -> CheckOptM (Map.Map Node res)
  }

invalidateAll :: (A.AST -> A.AST) -> CheckOptData -> CheckOptData
invalidateAll f d = d { ast = f (ast d), parItems = Nothing, nextVarsTouched = Map.empty,
  flowGraphRootsTerms = Nothing}

newtype CheckOptM a = CheckOptM (StateT CheckOptData PassM a)
  deriving (Monad, MonadIO)

instance Die CheckOptM where
  dieReport = CheckOptM . lift . dieReport

instance CSMR CheckOptM where
  getCompState = CheckOptM . lift $ getCompState

instance Warn CheckOptM where
  warnReport = CheckOptM . lift . warnReport

deCheckOptM :: CheckOptM a -> StateT CheckOptData PassM a
deCheckOptM (CheckOptM x) = x

newtype CheckOptM' t a = CheckOptM' (ReaderT (Route t A.AST) (RestartT CheckOptM) (Either t a))

instance Monad (CheckOptM' t) where
  return x = CheckOptM' (return (Right x))
  (>>=) m f = let (CheckOptM' m') = m in CheckOptM' $ do
    x <- m'
    case x of
      Left x -> return (Left x)
      Right x -> let CheckOptM' m'' = f x in m''

instance MonadIO (CheckOptM' t) where
  liftIO = CheckOptM' . liftM Right . liftIO

deCheckOptM' :: (t -> CheckOptM' t ()) -> (t, Route t A.AST) -> RestartT CheckOptM (Either
  t t)
deCheckOptM' f (x, r) = do
  x' <- runReaderT (let CheckOptM' m = f x in m) r
  case x' of
    Left replacement -> return (Left replacement)
    Right _ -> return (Right x)

-- | The idea is this: in normal operation you use the Right return value.  When
-- you want to restart the forAnyAST operation from a given point, you use the
-- Left constructor.
data Monad m => RestartT m a = RestartT { getRestartT :: m (Either () a) }

instance Monad m => Monad (RestartT m) where
  return x = RestartT $ return (Right x)
  (>>=) m f = let m' = getRestartT m in RestartT $ do
    x <- m'
    case x of
      Left route -> return (Left route)
      Right x' -> let m'' = getRestartT $ f x' in m''

instance MonadIO m => MonadIO (RestartT m) where
  liftIO f = RestartT $ (liftIO f) >>* Right

instance MonadTrans RestartT where
  lift = RestartT . liftM Right

instance Die m => Die (RestartT m) where
  dieReport = lift . dieReport

instance Die m => Die (ReaderT (Route t outer) m) where
  dieReport = lift . dieReport

instance Die (CheckOptM' t) where
  dieReport = liftCheckOptM . dieReport

instance Warn (CheckOptM' t) where
  warnReport = liftCheckOptM . warnReport

instance CSMR (CheckOptM' t) where
  getCompState = liftCheckOptM getCompState

askRoute :: CheckOptM' t (Route t A.AST)
askRoute = CheckOptM' $ ask >>* Right

getCheckOptData :: CheckOptM' t CheckOptData
getCheckOptData = CheckOptM' . lift . lift . CheckOptM $ get >>* Right

modifyCheckOptData :: (CheckOptData -> CheckOptData) -> CheckOptM' t ()
modifyCheckOptData = liftCheckOptM . CheckOptM . modify

liftCheckOptM :: CheckOptM a -> CheckOptM' t a
liftCheckOptM = CheckOptM' . liftM Right . lift . lift

forAnyParItems :: (ParItems a -> CheckOptM ()) -> CheckOptM ()
forAnyParItems = undefined


-- Like mkM, but with no return value, and this funny monad with routes, but also
-- we give an error if the plain function is ever triggered (given the typeset
-- stuff, it shouldn't be)
mkMR :: forall a. Data a => TransFunc a -> (forall b. Data b => TransFunc b)
mkMR f = plain `extMR` f
  where
    plain :: (forall c. Data c => TransFunc c)
    plain _ = dieP emptyMeta "Unexpected call of mkM_.plain"

-- Like extM, but with no return value, and this funny monad with routes:
extMR :: forall b. Data b =>
  (forall a. Data a => TransFunc a) ->
  (TransFunc b) ->
  (forall c. Data c => TransFunc c)
extMR generalF specificF (x, r) = case cast x of
  Nothing -> liftM (fromJust . cast) (generalF (x, unsafeCoerce# r))
  Just y -> liftM (fromJust . cast) (specificF (y, unsafeCoerce# r))

-- | This function currently only supports one type
forAnyAST :: forall a. Data a => (a -> CheckOptM' a ()) -> CheckOptM ()
forAnyAST origF = CheckOptM $ do
   tr <- get >>* ast
   doTree typeSet (mkMR (deCheckOptM' origF)) tr
  where
    typeSet :: TypeSet
    typeSet = makeTypeSet [typeKey (undefined :: a)]


forAnyASTStruct :: (forall a. Data a => (A.Structured a -> CheckOptM' (A.Structured
  a) ())) -> CheckOptM ()
forAnyASTStruct origF = CheckOptM $ do
   tr <- get >>* ast
   doTree typeSet allF tr
  where
    allF :: (forall c. Data c => TransFunc c)
    allF
      = mkMR    (deCheckOptM' (origF :: A.Structured A.Variant -> CheckOptM' (A.Structured A.Variant) ()))
        `extMR` (deCheckOptM' (origF :: A.Structured A.Process -> CheckOptM' (A.Structured A.Process) ()))
        `extMR` (deCheckOptM' (origF :: A.Structured A.Option -> CheckOptM' (A.Structured A.Option) ()))
        `extMR` (deCheckOptM' (origF :: A.Structured A.ExpressionList -> CheckOptM' (A.Structured A.ExpressionList) ()))
        `extMR` (deCheckOptM' (origF :: A.Structured A.Choice -> CheckOptM' (A.Structured A.Choice) ()))
        `extMR` (deCheckOptM' (origF :: A.Structured A.Alternative -> CheckOptM' (A.Structured A.Alternative) ()))
        `extMR` (deCheckOptM' (origF :: A.Structured () -> CheckOptM' (A.Structured ()) ()))
    
    typeSet :: TypeSet
    typeSet = makeTypeSet
      [typeKey (undefined :: A.Structured A.Variant)
      ,typeKey (undefined :: A.Structured A.Process)
      ,typeKey (undefined :: A.Structured A.Option)
      ,typeKey (undefined :: A.Structured A.ExpressionList)
      ,typeKey (undefined :: A.Structured A.Choice)
      ,typeKey (undefined :: A.Structured A.Alternative)
      ,typeKey (undefined :: A.Structured ())
      ]

type TransFunc a = (a, Route a A.AST) -> RestartT CheckOptM (Either a a)

-- | Given a TypeSet, a function to apply to everything of type a, a route
-- location to begin at and an AST, transforms the tree.  Handles any restarts
-- that are requested.
doTree :: TypeSet -> (forall a. Data a => TransFunc a) ->
      A.AST -> StateT CheckOptData PassM ()
doTree typeSet f tr
      = do x <- deCheckOptM (getRestartT (gmapMForRoute typeSet (apply typeSet f) tr >> return ()))
           case x of
             Left _ -> do -- Restart
               tr' <- get >>* ast
               doTree typeSet f tr'
             Right _ -> return ()


apply :: TypeSet -> (forall a. Data a => TransFunc a) ->
             (forall b. Data b => (b, Route b A.AST) -> RestartT CheckOptM b)
apply typeSet f (x, route)
      = do lift . CheckOptM $ modify $ \d -> if findMeta x == emptyMeta then d else d {lastValidMeta = findMeta x}
           z <- f' (x, route)
           gmapMForRoute typeSet (\(y, route') -> apply typeSet f (y, route @-> route')) z
  where
    -- Keep applying the function while there is a Left return (which indicates
    -- the value was replaced) until there is a Right return
    f' (x, route) = do
      x' <- f (x, route)
      case x' of
        Left y -> f' (y, route)
        Right y -> return y        

-- | For both of these functions I'm going to need to mark all analyses as no longer
-- valid, but more difficult will be to maintain the current position (if possible
-- -- should be in substitute, but not necessarily in replace) and continue.

-- | Substitutes the currently examined item for the given item, and continues
-- the traversal from the current point.  That is, the new item is transformed
-- again too.
substitute :: forall a. Data a => a -> CheckOptM' a ()
substitute x = CheckOptM' $ do
  r <- ask
  lift . lift . CheckOptM $ modify (invalidateAll $ routeSet r x)
  return (Left x)

--replaceBelow :: t -> t -> CheckOptM' a ()
--replaceEverywhere :: t -> t -> CheckOptM' a ()
-- TODO think about what this means (replace everywhere, or just children?)

-- Restarts the current forAnyAST from the top of the tree, but keeps all changes
-- made thus far.
restartForAnyAST :: CheckOptM' a a
restartForAnyAST = CheckOptM' . lift . RestartT $ return $ Left ()

runChecks :: CheckOptM () -> A.AST -> PassM A.AST
runChecks (CheckOptM m) x = execStateT m (CheckOptData {ast = x, parItems = Nothing,
  nextVarsTouched = Map.empty, flowGraphRootsTerms = Nothing, lastValidMeta = emptyMeta}) >>* ast

runChecksPass :: CheckOptM () -> Pass
runChecksPass c = pass "<Check>" [] [] (mkM (runChecks c))

--getParItems :: CheckOptM (ParItems ())
--getParItems = CheckOptM (\d -> Right (d, fromMaybe (generateParItems $ ast d) (parItems d)))

getParItems' :: CheckOptM' t (ParItems ())
getParItems' = todo

generateParItems :: A.AST -> ParItems ()
generateParItems = todo

-- | Performs the given action for the given child.  [0] is the first argument
-- of the current node's constructor, [2,1] is the second argument of the constructor
-- of the third argument of this constructor.  Issuing substitute inside this function
-- will yield an error.
withChild :: forall t a. [Int] -> CheckOptM' t a -> CheckOptM' t a
withChild ns (CheckOptM' m) = askRoute >>= (CheckOptM' . lift . inner)
  where
    inner :: Route t A.AST -> RestartT CheckOptM (Either t a)
    inner (Route rId rFunc) = runReaderT m (Route (rId ++ ns) (error "withChild attempted a substitution"))

-- | Searches forward in the graph from the given node to find all the reachable
-- nodes that have no successors, i.e. the terminal nodes
findTerminals :: Node -> Gr a b -> [Node]
findTerminals n g = nub [x | x <- dfs [n] g, null (suc g x)]

varsTouchedAfter :: FlowGraphAnalysis (Set.Set Var)
varsTouchedAfter = FlowGraphAnalysis
  nextVarsTouched (\x d -> d {nextVarsTouched = x `Map.union` nextVarsTouched d}) $ \(g, startNode) ->
    case findTerminals startNode g of
      [] -> return Map.empty
      [termNode] -> let connNodes = rdfs [termNode] g in
        case flowAlgorithm (funcs g) connNodes (termNode, Set.empty) of
          Left err -> dieP emptyMeta err
          Right nodesToVars -> {-(liftIO $ putStrLn $ "Graph:\n" ++ show g ++ "\n\nNodes:\n"
            ++ show (termNode, connNodes)) >> -}return nodesToVars
      ts -> dieP (fromMaybe emptyMeta $ fmap getNodeMeta $ lab g startNode) $ "Multiple terminal nodes in flow graph"
              ++ show [fmap getNodeMeta (lab g n) | n <- ts]
  where
    funcs :: FlowGraph CheckOptM UsageLabel -> GraphFuncs Node EdgeLabel (Set.Set Var)
    funcs g = GF     
      { nodeFunc = iterate g
      -- Backwards data flow:
      , nodesToProcess = lsuc g
      , nodesToReAdd = lpre g
      , defVal = Set.empty
      , userErrLabel = ("for node at: " ++) . show . fmap getNodeMeta . lab g
      }

    iterate :: FlowGraph CheckOptM UsageLabel ->
      (Node, EdgeLabel) -> Set.Set Var -> Maybe (Set.Set Var) -> Set.Set Var
    iterate g node prevVars maybeVars = case lab g (fst node) of
      Just ul ->
        let vs = nodeVars $ getNodeData ul
            readFromVars = readVars vs
            writtenToVars = writtenVars vs
            addTo = fromMaybe prevVars maybeVars
        in (readFromVars `Set.union` addTo) `Set.union` Map.keysSet writtenToVars
      Nothing -> error "Node label not found in calculateUsedAgainAfter"

  

getFlowGraph :: CheckOptM' t (FlowGraph CheckOptM UsageLabel, [Node], [Node])
getFlowGraph = getCache flowGraphRootsTerms (\x d -> d {flowGraphRootsTerms = Just x, nextVarsTouched
  = Map.empty}) generateFlowGraph

-- Makes sure that only the real last node at the end of a PROC/FUNCTION is a terminator
-- node, by joining any other nodes without successors to this node.  This is a
-- bit hacky, but is needed for some of the backwards flow analysis
correctFlowGraph :: Node -> (FlowGraph CheckOptM UsageLabel, [Node], [Node]) -> FlowGraph CheckOptM UsageLabel
correctFlowGraph curNode (g, roots, terms)
  = case findTerminals curNode g `intersect` terms of
      [] -> empty -- Not a PROC/FUNCTION
      [realTerm] -> foldl (addFakeEdge realTerm) g midTerms
  where
    -- The nodes that have no successors but are not the real terminator
    -- For example, the node after the last condition in an IF, or a STOP node
    midTerms = findTerminals curNode g \\ terms

    addFakeEdge :: Node -> FlowGraph CheckOptM UsageLabel -> Node -> FlowGraph CheckOptM UsageLabel
    addFakeEdge realTerm g n = insEdge (n, realTerm, ESeq Nothing) g

getCache :: (CheckOptData -> Maybe a) -> (a -> CheckOptData -> CheckOptData) -> (A.AST
  -> CheckOptM a) -> CheckOptM' t a
getCache getF setF genF = getCheckOptData >>= \x -> case getF x of
  Just y -> return y
  Nothing -> do y <- liftCheckOptM $ genF (ast x)
                modifyCheckOptData (setF y)
                return y

getCachedAnalysis :: Data t => FlowGraphAnalysis res -> CheckOptM' t (Maybe res)
getCachedAnalysis = getCachedAnalysis' (const True)

-- Analysis requires the latest flow graph, and uses this to produce a result
getCachedAnalysis' :: Data t => (UsageLabel -> Bool) -> FlowGraphAnalysis res -> CheckOptM' t (Maybe
  res)
getCachedAnalysis' f an = do
  d <- getCheckOptData
  g'@(g,_,_) <- getFlowGraph
  r <- askRoute
  -- Find the node that matches our location and the given function:
  case find (\(_,l) -> f (getNodeData l) && (getNodeRouteId l == routeId r)) (labNodes g) of
    Nothing -> (liftIO $ putStrLn $ "Could not find node for: " ++ show (lastValidMeta
      d)) >> return Nothing
    Just (n, _) ->
      case Map.lookup n (getFlowGraphAnalysis an d) of
        Just y -> return (Just y)
        Nothing -> liftCheckOptM $
                    do z <- doFlowGraphAnalysis an (correctFlowGraph n g', n)
                       CheckOptM $ modify $ addFlowGraphAnalysis an z
                       CheckOptM $ get >>* (Map.lookup n . getFlowGraphAnalysis an)

generateFlowGraph :: A.AST -> CheckOptM (FlowGraph CheckOptM UsageLabel, [Node],
  [Node])
generateFlowGraph x = buildFlowGraph labelUsageFunctions x >>= \g -> case g of
  Left err -> dieP emptyMeta err
  Right grt -> return grt

