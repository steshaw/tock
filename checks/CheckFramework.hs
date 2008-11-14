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

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.Generics
import Data.Graph.Inductive hiding (apply)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Control.Exception
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

newtype CheckOptM' t a = CheckOptM' (ReaderT (Route t A.AST) (RestartT CheckOptM) a)
  deriving (Monad, MonadIO)

deCheckOptM' :: CheckOptM' t a -> ReaderT (Route t A.AST) (RestartT CheckOptM) a
deCheckOptM' (CheckOptM' x) = x

-- | The idea is this: in normal operation you use the Right return value.  When
-- you want to restart the forAnyAST operation from a given point, you use the
-- Left constructor, supplying the route to use on the new tree (which you must
-- have put in the CheckOptM state).  If you wish
-- to start again from the top, supply routeIdentity, and your original function.
data Monad m => RestartT m a
  = RestartT { getRestartT :: m (Either [Int] a) }

instance Monad m => Monad (RestartT m) where
  return x = RestartT $ return $ Right x
  (>>=) m f = let m' = getRestartT m in RestartT $ do
    x <- m'
    case x of
      Left route -> return $ Left route
      Right x' -> let m'' = getRestartT $ f x' in m''

instance MonadIO m => MonadIO (RestartT m) where
  liftIO f = RestartT $ (liftIO f) >>* Right

instance MonadTrans RestartT where
  lift = RestartT . liftM Right

instance Die m => Die (ReaderT (Route t outer) m) where
  dieReport = lift . dieReport

instance Die (CheckOptM' t) where
  dieReport = liftCheckOptM . dieReport

instance Warn (CheckOptM' t) where
  warnReport = liftCheckOptM . warnReport

instance CSMR (CheckOptM' t) where
  getCompState = liftCheckOptM getCompState

askRoute :: CheckOptM' t (Route t A.AST)
askRoute = CheckOptM' $ ask

getCheckOptData :: CheckOptM' t CheckOptData
getCheckOptData = CheckOptM' . lift . lift . CheckOptM $ get

modifyCheckOptData :: (CheckOptData -> CheckOptData) -> CheckOptM' t ()
modifyCheckOptData = CheckOptM' . lift . lift . CheckOptM . modify

liftCheckOptM :: CheckOptM a -> CheckOptM' t a
liftCheckOptM = CheckOptM' . lift . lift

forAnyParItems :: (ParItems a -> CheckOptM ()) -> CheckOptM ()
forAnyParItems = undefined


-- Like mkM, but with no return value, and this funny monad with routes, but also
-- we give an error if the plain function is ever triggered (given the typeset
-- stuff, it shouldn't be)
mkM_ :: forall a. Data a => (a -> CheckOptM' a ()) -> (forall b. Data b => b -> CheckOptM'
  b ())
mkM_ f = plain `extM_` f
  where
    plain :: (forall c. Data c => c -> CheckOptM' c ())
    plain _ = dieP emptyMeta "Unexpected call of mkM_.plain"

-- Like extM, but with no return value, and this funny monad with routes:
extM_ :: forall b. Data b => (forall a. Data a => a -> CheckOptM' a ()) -> (b -> CheckOptM' b ())
  -> (forall c. Data c => c -> CheckOptM' c ())
extM_ generalF specificF x = case cast x of
  Nothing -> generalF x
  Just y -> let CheckOptM' z = specificF y in CheckOptM' $ ask >>= (lift . runReaderT z . unsafeCoerce#)


-- | This function currently only supports one type
forAnyAST :: forall a. Data a => (a -> CheckOptM' a ()) -> CheckOptM ()
forAnyAST origF = CheckOptM $ do
   tr <- get >>* ast
   doTree typeSet (mkM_ origF) [] tr
  where
    typeSet :: TypeSet
    typeSet = makeTypeSet [typeKey (undefined :: a)]


forAnyASTStruct :: (forall a. Data a => A.Structured a -> CheckOptM' (A.Structured
  a) ()) -> CheckOptM ()
forAnyASTStruct origF = CheckOptM $ do
   tr <- get >>* ast
   doTree typeSet allF [] tr
  where
    allF :: (forall c. Data c => c -> CheckOptM' c ())
    allF
      = mkM_    (origF :: A.Structured A.Variant -> CheckOptM' (A.Structured A.Variant) ())
        `extM_` (origF :: A.Structured A.Process -> CheckOptM' (A.Structured A.Process) ())
        `extM_` (origF :: A.Structured A.Option -> CheckOptM' (A.Structured A.Option) ())
        `extM_` (origF :: A.Structured A.ExpressionList -> CheckOptM' (A.Structured A.ExpressionList) ())
        `extM_` (origF :: A.Structured A.Choice -> CheckOptM' (A.Structured A.Choice) ())
        `extM_` (origF :: A.Structured A.Alternative -> CheckOptM' (A.Structured A.Alternative) ())
        `extM_` (origF :: A.Structured () -> CheckOptM' (A.Structured ()) ())
    
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



    -- | Given a TypeSet, a function to apply to everything of type a, a route
    -- location to begin at and an AST, transforms the tree.  Handles any restarts
    -- that are requested.
doTree :: TypeSet -> (forall a. Data a =>  a -> CheckOptM' a ()) ->
      [Int] -> A.AST -> StateT CheckOptData PassM ()
doTree typeSet f route tr
      = do x <- traverse typeSet f route tr
           case x of
             Left route' -> do -- Restart
               tr' <- get >>* ast
               doTree typeSet f route' tr'
             Right _ -> return ()

    -- | Given a TypeSet, a function to apply to everything of type a, a route
    -- location to begin at and an AST, transforms the tree.  If any restarts are
    -- requested, that is indicated in the return value.  If an AST is returned,
    -- it is ignored (all changes are done in the state)
traverse :: TypeSet -> (forall a. Data a => a -> CheckOptM' a ()) -> [Int] -> A.AST ->
      StateT CheckOptData PassM (Either [Int] ())
traverse typeSet f route tr
      = deCheckOptM . getRestartT $ 
          evalStateT (gen tr) (Just route)
      where
        -- We can't use routeModify with the route to jump to the right place,
        -- because then applying gen gets much more difficult, and I can't find
        -- a way through the maze of compiler errors.  So with a glorious hack,
        -- we tack on a state parameter with a (Maybe Route) and keep scanning
        -- until we find the place to resume from (or go one past it, which is
        -- nice in case the location is no longer valid)
        --
        -- TODO in future maybe I should try again to jump to the right spot

        -- Given a complete AST, either applies f (from parent) using apply (see
        -- below) if we are past the point we are meant to start at, or otherwise
        -- just skips this node
        gen :: A.AST -> StateT (Maybe [Int]) (RestartT CheckOptM) ()
        gen x = gmapMForRoute typeSet f' x >> return ()

        f' :: forall a. Data a => (a, Route a A.AST) -> StateT (Maybe [Int]) (RestartT
          CheckOptM) a
        f' (y, route) =
          do st <- get
             case st of
               -- We are past the target start point:
               Nothing -> lift $ apply typeSet f (y, route)
               Just targetRoute -> if routeId route < targetRoute
                 then return y {- Not reached start point yet -} else do
                   put Nothing -- Blank the start point now we've found it
                   lift $ apply typeSet f (y, route)

    -- The return of this function is ignored.  All changes should be done in the
    -- state.
apply :: TypeSet -> (forall a. Data a => a -> CheckOptM' a ()) ->
             (forall b. Data b => (b, Route b A.AST) -> RestartT CheckOptM b)
apply typeSet f (x, route)
      = (lift . CheckOptM $ modify $ \d -> if findMeta x == emptyMeta then d else d {lastValidMeta = findMeta x})
        >> (flip runReaderT route (deCheckOptM' (f x)))
        >> gmapMForRoute typeSet (\(y, route') -> apply typeSet f (y, route @-> route')) x

-- | For both of these functions I'm going to need to mark all analyses as no longer
-- valid, but more difficult will be to maintain the current position (if possible
-- -- should be in substitute, but not necessarily in replace) and continue.

-- | Substitutes the currently examined item for the given item, and continues
-- the traversal from the current point.  That is, the new item is transformed
-- again too.
substitute :: a -> CheckOptM' a ()
substitute x = CheckOptM' $ do
  r <- ask
  lift . lift . CheckOptM $ modify (invalidateAll $ routeSet r x)
  lift . RestartT $ return $ Left [] -- (routeId r)

--replaceBelow :: t -> t -> CheckOptM' a ()
--replaceEverywhere :: t -> t -> CheckOptM' a ()
-- TODO think about what this means (replace everywhere, or just children?)

-- Restarts the current forAnyAST from the top of the tree, but keeps all changes
-- made thus far.
restartForAnyAST :: CheckOptM' a a
restartForAnyAST = CheckOptM' . lift . RestartT $ return $ Left []

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
withChild :: forall t a. [Int] -> CheckOptM' () a -> CheckOptM' t a
withChild ns (CheckOptM' m) = askRoute >>= (CheckOptM' . lift . RestartT . inner)
  where
    inner :: Route t A.AST -> CheckOptM (Either [Int] a)
    inner (Route rId rFunc) = getRestartT $ runReaderT m (Route (rId ++ ns) (error "withChild attempted a substitution"))

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

