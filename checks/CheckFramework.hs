{-
Tock: a compiler for parallel languages
Copyright (C) 2008, 2009  University of Kent

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

module CheckFramework (CheckOptM, CheckOptASTM, forAnyASTTopDown, forAnyASTStructTopDown, substitute, restartForAnyAST,
  CheckOptASTM',
  forAnyASTStructBottomUpAccum,
  askAccum,
  runChecks, runChecksPass, getFlowGraph, withChild, varsTouchedAfter,
  getCachedAnalysis, getCachedAnalysis',
  forAnyFlowNode, getFlowLabel, getFlowMeta, CheckOptFlowM) where

import Control.Monad.Reader
import Control.Monad.State
import Data.Generics (Data)
import Data.Graph.Inductive hiding (apply)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import qualified AST as A
import CompState
import Data.Generics.Alloy.Route
import Errors
import FlowAlgorithms
import FlowGraph
import FlowUtils
import Metadata
import Pass
import Traversal
import UsageCheckUtils
import Utils

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

instance MonadState CompState CheckOptM where
  get = CheckOptM $ lift get
  put = CheckOptM . lift . put

instance CSMR CheckOptM where
  getCompState = CheckOptM . lift $ getCompState

instance Warn CheckOptM where
  warnReport = CheckOptM . lift . warnReport

deCheckOptM :: CheckOptM a -> StateT CheckOptData PassM a
deCheckOptM (CheckOptM x) = x

newtype CheckOptASTM' acc t a = CheckOptASTM' (ReaderT (acc, Route t A.AST) (RestartT CheckOptM) (Either t a))

type CheckOptASTM = CheckOptASTM' ()

instance Monad (CheckOptASTM' acc t) where
  return x = CheckOptASTM' (return (Right x))
  (>>=) m f = let (CheckOptASTM' m') = m in CheckOptASTM' $ do
    x <- m'
    case x of
      Left x -> return (Left x)
      Right x -> let CheckOptASTM' m'' = f x in m''

instance MonadIO (CheckOptASTM' acc t) where
  liftIO = CheckOptASTM' . liftM Right . liftIO

instance MonadState CompState (CheckOptASTM' acc t) where
  get = CheckOptASTM' . liftM Right . lift . lift $ get
  put = CheckOptASTM' . liftM Right . lift . lift . put

deCheckOptASTM' :: (t -> CheckOptASTM' acc t ()) -> (t, Route t A.AST, acc) -> RestartT CheckOptM (Either
  t t)
deCheckOptASTM' f (x, r, acc) = do
  x' <- runReaderT (let CheckOptASTM' m = f x in m) (acc, r)
  case x' of
    Left replacement -> return (Left replacement)
    Right _ -> return (Right x)

deCheckOptASTM :: (t -> CheckOptASTM t ()) -> (t, Route t A.AST) -> RestartT CheckOptM (Either
  t t)
deCheckOptASTM f (x, r) = deCheckOptASTM' f (x,r,())


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

instance Die (CheckOptASTM' acc t) where
  dieReport = liftCheckOptM . dieReport

instance Warn (CheckOptASTM' acc t) where
  warnReport = liftCheckOptM . warnReport

instance CSMR (CheckOptASTM' acc t) where
  getCompState = liftCheckOptM getCompState

instance MonadState CompState (CheckOptFlowM t) where
  get = CheckOptFlowM . lift $ get
  put = CheckOptFlowM . lift . put

askRoute :: CheckOptASTM' acc t (Route t A.AST)
askRoute = CheckOptASTM' $ ask >>* snd >>* Right

askAccum :: CheckOptASTM' acc t acc
askAccum = CheckOptASTM' $ ask >>* fst >>* Right

getCheckOptData :: CheckOptM CheckOptData
getCheckOptData = CheckOptM get

modifyCheckOptData :: (CheckOptData -> CheckOptData) -> CheckOptM ()
modifyCheckOptData = CheckOptM . modify

liftCheckOptM :: CheckOptM a -> CheckOptASTM' acc t a
liftCheckOptM = CheckOptASTM' . liftM Right . lift . lift

-- Could also include the list of connected nodes in the reader monad:
newtype CheckOptFlowM t a = CheckOptFlowM (ReaderT (Node, Map.Map Node t) CheckOptM a)
  deriving (Monad, MonadIO)

instance Die m => Die (ReaderT (Node, Map.Map Node a) m) where
  dieReport = lift . dieReport

instance CSMR (CheckOptFlowM t) where
  getCompState = CheckOptFlowM $ lift getCompState

instance Warn (CheckOptFlowM t) where
  warnReport = CheckOptFlowM . lift . warnReport


forAnyFlowNode :: ((FlowGraph CheckOptM UsageLabel, [Node], [Node]) -> CheckOptM
  (Map.Map Node t)) -> CheckOptFlowM t () -> CheckOptM ()
forAnyFlowNode fgraph (CheckOptFlowM f) =
  do grt@(g,_,_) <- getFlowGraph
     m <- fgraph grt
     sequence_ [runReaderT f (n, m)  | n <- nodes g]

getFlowLabel :: CheckOptFlowM t (UsageLabel, Maybe t)
getFlowLabel = CheckOptFlowM $
  do (n, m) <- ask
     (g,_,_) <- lift getFlowGraph
     l <- checkJust (Nothing, "Label not in flow graph") $ lab g n
     return (getNodeData l, Map.lookup n m)

getFlowMeta :: CheckOptFlowM t Meta
getFlowMeta = CheckOptFlowM $
  do (n, _) <- ask
     (g,_,_) <- lift getFlowGraph
     case lab g n of
       Nothing -> return emptyMeta
       Just l -> return $ getNodeMeta l

-- | This function currently only supports one type
forAnyASTTopDown :: forall a.
  (AlloyARoute A.AST (a :-@ BaseOpMRoute) BaseOpMRoute
  ,AlloyARoute a BaseOpMRoute (a :-@ BaseOpMRoute)
  ) =>
    (a -> CheckOptASTM a ()) -> CheckOptM ()
forAnyASTTopDown origF = CheckOptM $ do
   tr <- get >>* ast
   doTree ops transformMRoute tr
     where
       ops = (makeTopDownMRoute ops $ keepApplying $ deCheckOptASTM origF) :-@ baseOpMRoute

forAnyASTStructTopDown :: (forall a. Data a => (A.Structured a -> CheckOptASTM (A.Structured
  a) ())) -> CheckOptM ()
forAnyASTStructTopDown origF = CheckOptM $ do
   tr <- get >>* ast
   doTree ops transformMRoute tr
  where
    ops
      = (makeTopDownMRoute ops $ keepApplying $ deCheckOptASTM (origF :: A.Structured A.Variant -> CheckOptASTM (A.Structured A.Variant) ()))
        :-@ (makeTopDownMRoute ops $ keepApplying $ deCheckOptASTM (origF :: A.Structured A.Process -> CheckOptASTM (A.Structured A.Process) ()))
        :-@ (makeTopDownMRoute ops $ keepApplying $ deCheckOptASTM (origF :: A.Structured A.Option -> CheckOptASTM (A.Structured A.Option) ()))
        :-@ (makeTopDownMRoute ops $ keepApplying $ deCheckOptASTM (origF :: A.Structured A.ExpressionList -> CheckOptASTM (A.Structured A.ExpressionList) ()))
        :-@ (makeTopDownMRoute ops $ keepApplying $ deCheckOptASTM (origF :: A.Structured A.Choice -> CheckOptASTM (A.Structured A.Choice) ()))
        :-@ (makeTopDownMRoute ops $ keepApplying $ deCheckOptASTM (origF :: A.Structured A.Alternative -> CheckOptASTM (A.Structured A.Alternative) ()))
        :-@ (makeTopDownMRoute ops $ keepApplying $ deCheckOptASTM (origF :: A.Structured () -> CheckOptASTM (A.Structured ()) ()))
        :-@ baseOpMRoute

type AccumOps b = b :-@ StructOps

type StructOps =
      A.Structured A.Variant
  :-@ A.Structured A.Process
  :-@ A.Structured A.Option
  :-@ A.Structured A.ExpressionList
  :-@ A.Structured A.Choice
  :-@ A.Structured A.Alternative
  :-@ A.Structured ()
  :-@ BaseOpMRoute

type SingleOps b
  = b :-@ BaseOpMRoute

type AccumMap b = Map.Map [Int] b

findSub :: [Int] -> AccumMap b -> [b]
findSub r m = [v | (k, v) <- Map.toList m, r `isPrefixOf` k]
  -- TODO this could be made more efficient by picking out a range in the map

filterSub :: [Int] -> AccumMap b -> AccumMap b
filterSub r = Map.filterWithKey (\k _ -> not $ r `isPrefixOf` k)

-- I know the constraints here look horrendous, but it's really just three groups.
forAnyASTStructBottomUpAccum :: forall b. (Data b,
  -- Allow us to descend into the AST with our full set of ops:
  AlloyARoute A.AST (AccumOps b) BaseOpMRoute,

  -- Allow us to recurse into each Structured item (and b) with our full set of
  -- ops:
  AlloyARoute (A.Structured A.Variant) BaseOpMRoute (AccumOps b),
  AlloyARoute (A.Structured A.Process) BaseOpMRoute (AccumOps b),
  AlloyARoute (A.Structured A.Option) BaseOpMRoute (AccumOps b),
  AlloyARoute (A.Structured A.ExpressionList) BaseOpMRoute (AccumOps b),
  AlloyARoute (A.Structured A.Choice) BaseOpMRoute (AccumOps b),
  AlloyARoute (A.Structured A.Alternative) BaseOpMRoute (AccumOps b),
  AlloyARoute (A.Structured ()) BaseOpMRoute (AccumOps b),
  AlloyARoute b BaseOpMRoute (AccumOps b),

  -- Allow us to descend into each Structured item with just our ops for
  -- b, when our accumulated stuff becomes invalidated
  AlloyARoute (A.Structured A.Variant) (SingleOps b) BaseOpMRoute,
  AlloyARoute (A.Structured A.Process) (SingleOps b) BaseOpMRoute,
  AlloyARoute (A.Structured A.Option) (SingleOps b) BaseOpMRoute,
  AlloyARoute (A.Structured A.ExpressionList) (SingleOps b) BaseOpMRoute,
  AlloyARoute (A.Structured A.Choice) (SingleOps b) BaseOpMRoute,
  AlloyARoute (A.Structured A.Alternative) (SingleOps b) BaseOpMRoute,
  AlloyARoute (A.Structured ()) (SingleOps b) BaseOpMRoute,
  -- For b, we will recurse, not descend:
  AlloyARoute b BaseOpMRoute (SingleOps b)

  ) =>
  (forall a. Data a => (A.Structured a) -> CheckOptASTM' [b] (A.Structured a) ()) -> CheckOptM ()
forAnyASTStructBottomUpAccum origF = CheckOptM $ do
   tr <- get >>* ast
   doTree ops (\x y z -> flip evalStateT (Map.empty :: AccumMap b) $ transformMRoute x y z) tr
  where
    ops :: AccumOps b (StateT (AccumMap b) (RestartT CheckOptM)) A.AST
    ops = applyAccum (undefined::b) allF

    keepApplying' ::
      AlloyARoute t (b :-@ BaseOpMRoute)
         BaseOpMRoute
      => ((t, Route t A.AST) -> StateT (AccumMap b) (RestartT CheckOptM) (Either t t)) ->
         ((t, Route t A.AST) -> StateT (AccumMap b) (RestartT CheckOptM) t)
    keepApplying' f xr = do x' <- f xr
                            case x' of
                              Right y -> return y
                              Left y -> do -- remove all sub-items from state,
                                           -- and then scan the item anew:
                                           modify $ filterSub (routeId $ snd xr)
                                           transformMRoute (applyAccum (undefined::b) baseOpMRoute) baseOpMRoute (y, snd xr)
                                           keepApplying' f (y, snd xr)

    wrap :: forall a. (Data a,
        AlloyARoute (A.Structured a) BaseOpMRoute (AccumOps b)
        , AlloyARoute (A.Structured a) (b :-@ BaseOpMRoute) BaseOpMRoute 
      ) => ((A.Structured a, Route (A.Structured a) A.AST, [b]) -> RestartT
      CheckOptM (Either (A.Structured a) (A.Structured a))) -> (A.Structured a, Route (A.Structured
        a) A.AST) -> StateT (AccumMap b) (RestartT
        CheckOptM) (A.Structured a)
    wrap f = makeBottomUpMRoute ops $ keepApplying' $ \(x, y) -> get >>= \z -> lift (f (x, y, findSub
      (routeId y) z))

    allF
      = (wrap $ deCheckOptASTM' (origF :: (A.Structured A.Variant) ->
                      CheckOptASTM' [b] (A.Structured A.Variant) ()))
        :-@ (wrap $ deCheckOptASTM' (origF :: (A.Structured A.Process) ->
                      CheckOptASTM' [b] (A.Structured A.Process) ()))
        :-@ (wrap $ deCheckOptASTM' (origF :: (A.Structured A.Option) ->
                      CheckOptASTM' [b] (A.Structured A.Option) ()))
        :-@ (wrap $ deCheckOptASTM' (origF :: (A.Structured A.ExpressionList) ->
                      CheckOptASTM' [b] (A.Structured A.ExpressionList) ()))
        :-@ (wrap $ deCheckOptASTM' (origF :: (A.Structured A.Choice) ->
                      CheckOptASTM' [b] (A.Structured A.Choice) ()))
        :-@ (wrap $ deCheckOptASTM' (origF :: (A.Structured A.Alternative) ->
                      CheckOptASTM' [b] (A.Structured A.Alternative) ()))
        :-@ (wrap $ deCheckOptASTM' (origF :: (A.Structured ()) ->
                      CheckOptASTM' [b] (A.Structured ()) ()))
        :-@ baseOpMRoute

-- | Given a TypeSet, a function to apply to everything of type a, a route
-- location to begin at and an AST, transforms the tree.  Handles any restarts
-- that are requested.
doTree :: ops ->
  (ops -> BaseOpMRoute m outer -> (A.AST, Route A.AST A.AST) -> RestartT CheckOptM A.AST) -> A.AST -> StateT CheckOptData PassM ()
           -- This line applies "apply" to the first thing of the right type in
           -- the given AST; from there, ops recurses for itself
doTree ops trans tr
      = do x <- deCheckOptM (getRestartT (trans ops baseOpMRoute (tr, identityRoute) >> return ()))
           case x of
             Left _ -> do -- Restart
               tr' <- get >>* ast
               doTree ops trans tr'
             Right _ -> return ()

applyAccum :: forall t ops.
  AlloyARoute t BaseOpMRoute (t :-@ ops)
  => t -> ops (StateT (AccumMap t) (RestartT CheckOptM)) A.AST -> (t :-@ ops)
    (StateT (AccumMap t) (RestartT CheckOptM)) A.AST
applyAccum _ ops = ops'
  where
    ops' :: (t :-@ ops) (StateT (AccumMap t) (RestartT CheckOptM)) A.AST
    ops' = accum :-@ ops

    accum xr = do x' <- transformMRoute baseOpMRoute ops' xr
                  modify $ Map.insert (routeId $ snd xr) x'
                  return x'

-- Keep applying the function while there is a Left return (which indicates
-- the value was replaced) until there is a Right return
keepApplying :: Monad m => ((t, Route t outer) -> m (Either t t)) -> ((t, Route t outer) -> m t)
keepApplying f (x, route) = do
      x' <- f (x, route)
      case x' of
        Left y -> keepApplying f (y, route)
        Right y -> return y

-- | For both of these functions I'm going to need to mark all analyses as no longer
-- valid, but more difficult will be to maintain the current position (if possible
-- -- should be in substitute, but not necessarily in replace) and continue.

-- | Substitutes the currently examined item for the given item, and continues
-- the traversal from the current point.  That is, the new item is transformed
-- again too.
substitute :: forall a acc. Data a => a -> CheckOptASTM' acc a ()
substitute x = CheckOptASTM' $ do
  r <- ask >>* snd
  lift . lift . CheckOptM $ modify (invalidateAll $ routeSet r x)
  return (Left x)

--replaceBelow :: t -> t -> CheckOptASTM a ()
--replaceEverywhere :: t -> t -> CheckOptASTM a ()
-- TODO think about what this means (replace everywhere, or just children?)

-- Restarts the current forAnyAST from the top of the tree, but keeps all changes
-- made thus far.
restartForAnyAST :: CheckOptASTM' acc a a
restartForAnyAST = CheckOptASTM' . lift . RestartT $ return $ Left ()

runChecks :: CheckOptM () -> A.AST -> PassM A.AST
runChecks (CheckOptM m) x = execStateT m (CheckOptData {ast = x, parItems = Nothing,
  nextVarsTouched = Map.empty, flowGraphRootsTerms = Nothing, lastValidMeta = emptyMeta}) >>* ast

runChecksPass :: CheckOptM () -> Pass A.AST
runChecksPass c = pass "<Check>" [] [] (runChecks c)

--getParItems :: CheckOptM (ParItems ())
--getParItems = CheckOptM (\d -> Right (d, fromMaybe (generateParItems $ ast d) (parItems d)))

-- | Performs the given action for the given child.  [0] is the first argument
-- of the current node's constructor, [2,1] is the second argument of the constructor
-- of the third argument of this constructor.  Issuing substitute inside this function
-- will yield an error.
withChild :: forall acc t a. [Int] -> CheckOptASTM' acc t a -> CheckOptASTM' acc t a
withChild ns (CheckOptASTM' m) = askRoute >>= (CheckOptASTM' . lift . inner)
  where
    inner :: Route t A.AST -> RestartT CheckOptM (Either t a)
    inner r = runReaderT m (error "withChild asked for accum",
      makeRoute (routeId r) (error "withChild attempted a substitution"))

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
    iterate g node varsForPrevNode maybeVars = case lab g (fst node) of
      Just ul ->
        let vs = nodeVars $ getNodeData ul
            readFromVars = readVars vs
            writtenToVars = writtenVars vs
            addTo =  fromMaybe Set.empty maybeVars
        in foldl Set.union addTo [varsForPrevNode, readFromVars, Map.keysSet writtenToVars]
      Nothing -> error "Node label not found in calculateUsedAgainAfter"

  

getFlowGraph :: CheckOptM (FlowGraph CheckOptM UsageLabel, [Node], [Node])
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
  -> CheckOptM a) -> CheckOptM a
getCache getF setF genF = getCheckOptData >>= \x -> case getF x of
  Just y -> return y
  Nothing -> do y <- genF (ast x)
                modifyCheckOptData (setF y)
                return y

getCachedAnalysis :: Data t => FlowGraphAnalysis res -> CheckOptASTM t (Maybe res)
getCachedAnalysis = getCachedAnalysis' (const True)

-- Analysis requires the latest flow graph, and uses this to produce a result
getCachedAnalysis' :: Data t => (UsageLabel -> Bool) -> FlowGraphAnalysis res -> CheckOptASTM t (Maybe
  res)
getCachedAnalysis' f an = do
  d <- liftCheckOptM getCheckOptData
  g'@(g,_,_) <- liftCheckOptM getFlowGraph
  r <- askRoute
  -- Find the node that matches our location and the given function:
  case find (\(_,l) -> f (getNodeData l) && (getNodeRouteId l == routeId r)) (labNodes g) of
    Nothing -> {- (liftIO $ putStrLn $ "Could not find node for: " ++ show (lastValidMeta
      d)) >> -} return Nothing
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

