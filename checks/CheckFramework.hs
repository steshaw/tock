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

module CheckFramework (CheckOptM, CheckOptM', forAnyAST, substitute, restartForAnyAST,
  runChecks, runChecksPass, getFlowGraphAndMap, withChild, varsTouchedAfter,
  getCachedAnalysis, getCachedAnalysis') where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.Generics
import Data.Graph.Inductive
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Control.Exception

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

data CheckOptData = CheckOptData
 { ast :: A.AST
 , parItems :: Maybe (ParItems ())
  -- TODO need to split this up per connected subgraphs
 , nextVarsTouched :: Maybe (Map.Map Node (Set.Set Var))
 , flowGraph :: Maybe (FlowGraph CheckOptM UsageLabel)
 }

--TODO make this a data item that fiddles with CheckOptData
data FlowGraphAnalysis res = FlowGraphAnalysis
  { getFlowGraphAnalysis :: CheckOptData -> Maybe (Map.Map Node res)
  , setFlowGraphAnalysis :: Map.Map Node res -> CheckOptData -> CheckOptData
  , doFlowGraphAnalysis :: (FlowGraph CheckOptM UsageLabel, Node) -> CheckOptM (Map.Map Node res)
  }

invalidateAll :: (A.AST -> A.AST) -> CheckOptData -> CheckOptData
invalidateAll f d = d { ast = f (ast d), parItems = Nothing, nextVarsTouched = Nothing,
  flowGraph = Nothing}

newtype CheckOptM a = CheckOptM (StateT CheckOptData PassM a)
  deriving (Monad, MonadIO)

instance Die CheckOptM where
  dieReport = CheckOptM . lift . dieReport

instance CSMR CheckOptM where
  getCompState = CheckOptM . lift $ getCompState

deCheckOptM :: CheckOptM a -> StateT CheckOptData PassM a
deCheckOptM (CheckOptM x) = x

newtype CheckOptM' t a = CheckOptM' (RestartT A.AST t CheckOptM a)
  deriving (Monad, MonadIO)

deCheckOptM' :: CheckOptM' t a -> RestartT A.AST t CheckOptM a
deCheckOptM' (CheckOptM' x) = x

-- | The idea is this: in normal operation you use the Right return value.  When
-- you want to restart the forAnyAST operation from a given point, you use the
-- Left constructor, supplying the route to use on the new tree (which you must
-- have put in the CheckOptM state) and the continuation to apply.  If you wish
-- to start again from the top, supply routeIdentity, and your original function.
data Monad m => RestartT outer t m a = RestartT { getRestartT :: ReaderT (Route
  t outer) m (Either (Maybe (Route t outer), t -> RestartT outer t m a) a) }

instance Monad m => Monad (RestartT outer t m) where
  return x = RestartT $ return $ Right x
  (>>=) m f = let m' = getRestartT m in RestartT $ do
    x <- m'
    case x of
      Left (route, cont) -> return $ Left (route, f <.< cont)
      Right x' -> let m'' = getRestartT $ f x' in m''

instance MonadIO m => MonadIO (RestartT outer t m) where
  liftIO f = RestartT $ lift (liftIO f) >>= (return . Right)

instance MonadTrans (RestartT outer t) where
  lift = RestartT . liftM Right . lift

instance Die m => Die (ReaderT (Route t outer) m) where
  dieReport = lift . dieReport

instance Die (CheckOptM' t) where
  dieReport = liftCheckOptM . dieReport

askRoute :: CheckOptM' t (Route t A.AST)
askRoute = CheckOptM' . RestartT . liftM Right $ ask

getCheckOptData :: CheckOptM' t CheckOptData
getCheckOptData = CheckOptM' . RestartT . lift . CheckOptM $ get >>* Right

modifyCheckOptData :: (CheckOptData -> CheckOptData) -> CheckOptM' t ()
modifyCheckOptData = CheckOptM' . RestartT . lift . CheckOptM . liftM Right . modify

liftCheckOptM :: CheckOptM a -> CheckOptM' t a
liftCheckOptM = CheckOptM' . RestartT . lift . liftM Right

liftRestartT :: Monad m => m a -> RestartT outer t m a
liftRestartT m = RestartT $ lift (m >>* Right)

--elseError :: Bool -> String -> CheckOptM ()
--elseError b err = CheckOptM $ if b then lift $ dieP emptyMeta err else return ()
--  TODO use the nearest available meta-tag in the current data

forAnyParItems :: (ParItems a -> CheckOptM ()) -> CheckOptM ()
forAnyParItems = undefined

-- | This function currently only supports one type
forAnyAST :: forall a. Data a => (a -> CheckOptM' a ()) -> CheckOptM ()
forAnyAST origF = CheckOptM $ do
   tr <- get >>* ast
   doTree typeSet (deCheckOptM' . origF) [] tr
  where
    typeSet :: TypeSet
    typeSet = makeTypeSet [typeKey (undefined :: a)]

    -- | Given a TypeSet, a function to apply to everything of type a, a route
    -- location to begin at and an AST, transforms the tree.  Handles any restarts
    -- that are requested.
    doTree :: TypeSet -> (a -> RestartT A.AST a CheckOptM ()) ->
      [Int] -> A.AST -> StateT CheckOptData PassM ()
    doTree typeSet f route tr
      = do x <- traverse typeSet f (Just route) tr
           case x of
             Left (route', cont) -> do -- Restart
               tr' <- get >>* ast
               doTree typeSet (\x -> cont x >> return ()) (maybe [] routeId route') tr'
             Right _ -> return ()

    -- | Given a TypeSet, a function to apply to everything of type a, a route
    -- location to begin at and an AST, transforms the tree.  If any restarts are
    -- requested, that is indicated in the return value
    traverse :: TypeSet -> (a -> RestartT A.AST a CheckOptM ()) -> Maybe [Int] -> A.AST ->
      StateT CheckOptData PassM
        (Either (Maybe (Route a A.AST), a -> RestartT A.AST a CheckOptM A.AST) A.AST)
    traverse typeSet f route tr
      = deCheckOptM $ flip runReaderT undefined
          -- We use undefined because we don't have a real default value, and the user-supplied
          -- function will only be called from inside a "local".  Perhaps with
          -- some rearrangement we could remove this awkwardness (runReaderT instead
          -- of local).
          (getRestartT $ flip evalStateT (case route of
             Just r -> Just r
             Nothing -> Just [] -- No route, means start from the beginning
          ) $ gen tr)
      where
        -- We can't use routeModify with the route to jump to the right place,
        -- because then applying gen gets much more difficult, and I can't find
        -- a way through the maze of compiler errors.  So with a glorious hack,
        -- we tack on a state parameter with a (Maybe Route) and keep scanning
        -- until we find the place to resume from (or go one past it, which is
        -- nice in case the location is no longer valid)
        
        gen :: A.AST -> StateT (Maybe [Int]) (RestartT A.AST a CheckOptM) A.AST
        gen x = gmapMForRoute typeSet (baseTransformRoute `extTransformRoute` (\(y, route) ->
          do st <- get
             case st of
               -- We are past the target start point:
               Nothing -> lift $ apply typeSet f (y, route)
               Just targetRoute -> if targetRoute > routeId route
                 then return y {- Not reached start point yet -} else do
                   put Nothing -- Blank the start point now we've found it
                   lift $ apply typeSet f (y, route)
          )) x

    -- The return of this function is ignored.  All changes should be done in the
    -- state.
    apply :: TypeSet -> (a -> RestartT A.AST a CheckOptM ()) ->
             (a, Route a A.AST) -> RestartT A.AST a CheckOptM a
    apply typeSet f (x, route)
      = (RestartT $ (local (const route) $ getRestartT (f x)))
        >> (liftRestartT (CheckOptM get) >>* ast >>* routeGet route)
        >>= gmapMForRoute typeSet (extTransformRoute baseTransformRoute $
              \(y, route') -> apply typeSet f (y, route @-> route'))

-- | For both of these functions I'm going to need to mark all analyses as no longer
-- valid, but more difficult will be to maintain the current position (if possible
-- -- should be in substitute, but not necessarily in replace) and continue.

-- | Substitutes the currently examined item for the given item, and continues
-- the traversal from the current point.  That is, the new item is transformed
-- again too.
substitute :: a -> CheckOptM' a ()
substitute x = CheckOptM' . RestartT $ do
  r <- ask
  lift $ CheckOptM $ modify (invalidateAll $ routeSet r x)
  return $ Left (Just r, const $ return ())

--replaceBelow :: t -> t -> CheckOptM' a ()
--replaceEverywhere :: t -> t -> CheckOptM' a ()
-- TODO think about what this means (replace everywhere, or just children?)

-- Restarts the current forAnyAST from the top of the tree, but keeps all changes
-- made thus far.
restartForAnyAST :: CheckOptM' a a
restartForAnyAST = CheckOptM' $ RestartT $ return $ Left (Nothing, return)

runChecks :: CheckOptM () -> A.AST -> PassM A.AST
runChecks (CheckOptM m) x = execStateT m (CheckOptData {ast = x, parItems = Nothing,
  nextVarsTouched = Nothing, flowGraph = Nothing}) >>* ast

runChecksPass :: CheckOptM () -> Pass
runChecksPass c = pass "<Check>" [] [] (mkM (runChecks c))

--getParItems :: CheckOptM (ParItems ())
--getParItems = CheckOptM (\d -> Right (d, fromMaybe (generateParItems $ ast d) (parItems d)))

getParItems' :: CheckOptM' t (ParItems ())
getParItems' = todo

generateParItems :: A.AST -> ParItems ()
generateParItems = todo

withChild :: forall t a. [Int] -> CheckOptM' () a -> CheckOptM' t a
withChild ns (CheckOptM' (RestartT m)) = askRoute >>= \r -> CheckOptM' $ RestartT $ inner r
  where
    inner :: Route t A.AST -> ReaderT (Route t A.AST) CheckOptM
      (Either (Maybe (Route t A.AST), t -> RestartT A.AST t CheckOptM a) a)
    inner r = liftM munge $ lift $ runReaderT m (Route (routeId r ++ ns) undefined)

    munge :: Either (Maybe (Route () A.AST), () -> RestartT A.AST () CheckOptM a) a
      -> Either (Maybe (Route t A.AST), t -> RestartT A.AST t CheckOptM a) a
    munge (Right x) = Right x
    munge (Left _) = Left $ error "withChild wants to restart, help!"

{-
getVarsTouchedAfter :: CheckOptM' t (Set.Set Var)
getVarsTouchedAfter = do
  r <- askRoute >>* routeId
  nu <- getCachedAnalysis varsTouchedAfter
  case Map.lookup r nu of
    Nothing -> dieP emptyMeta "Node not found in flow graph"
    Just vs -> return vs
-}

varsTouchedAfter :: FlowGraphAnalysis (Set.Set Var)
varsTouchedAfter = FlowGraphAnalysis
  nextVarsTouched (\x d -> d {nextVarsTouched = Just x}) $ \(g, startNode) ->
    case flowAlgorithm (funcs g) (rdfs [startNode] g) (startNode, Set.empty) of
      Left err -> dieP emptyMeta err
      Right nodesToVars -> (liftIO $ putStrLn $ show g) >> return nodesToVars
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

  

--getLastPlacesWritten :: CheckOptM' t [(Route, Maybe A.Expression)]

getFlowGraphAndMap :: CheckOptM' t (FlowGraph CheckOptM UsageLabel)
getFlowGraphAndMap = getCache flowGraph (\x d -> d {flowGraph = Just x}) generateFlowGraph
-- TODO make this invalidate all the analyses

getCache :: (CheckOptData -> Maybe a) -> (a -> CheckOptData -> CheckOptData) -> (A.AST
  -> CheckOptM a) -> CheckOptM' t a
getCache getF setF genF = getCheckOptData >>= \x -> case getF x of
  Just y -> return y
  Nothing -> do y <- liftCheckOptM $ genF (ast x)
                modifyCheckOptData (setF y)
                return y

getCachedAnalysis :: FlowGraphAnalysis res -> CheckOptM' t res
getCachedAnalysis = getCachedAnalysis' (const True)

-- Analysis requires the latest flow graph, and uses this to produce a result
getCachedAnalysis' :: (UsageLabel -> Bool) -> FlowGraphAnalysis res -> CheckOptM' t res
getCachedAnalysis' f an = do
  d <- getCheckOptData
  g <- getFlowGraphAndMap
  r <- askRoute >>* routeId
  -- Find the node that matches our location and the given function:
  case find (\(_,l) -> f (getNodeData l) && (getNodeRouteId l == r)) (labNodes g) of
    Nothing -> dieP emptyMeta $ "Node not found in flow graph: " ++ show g
    Just (n, _) -> do
      m <- case getFlowGraphAnalysis an d of
        Just y -> return y
        Nothing -> liftCheckOptM $
                    do z <- doFlowGraphAnalysis an (g, n)
                       CheckOptM $ modify $ setFlowGraphAnalysis an z
                       return z
      case Map.lookup n m of
        Nothing -> dieP emptyMeta "Node not found in analysis results"
        Just r -> return r

generateFlowGraph :: A.AST -> CheckOptM (FlowGraph CheckOptM UsageLabel)
generateFlowGraph x = buildFlowGraph labelUsageFunctions x >>= \g -> case g of
  Left err -> dieP emptyMeta err
  Right (y,_,_) -> return y
