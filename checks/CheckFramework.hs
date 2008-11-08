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

module CheckFramework where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.Generics
import Data.Maybe
import Control.Exception

import qualified AST as A
import UsageCheckUtils
import GenericUtils
import Traversal
import Utils

data CheckOptData = CheckOptData
 { ast :: A.AST
 , parItems :: Maybe (ParItems ())
 -- TODO also keep track of our location in each data structure
 }

invalidateAll :: CheckOptData -> A.AST -> CheckOptData
invalidateAll d t = d { ast = t, parItems = Nothing}

newtype CheckOptM a = CheckOptM (ErrorT String (State CheckOptData) a)
  deriving (Monad, MonadError String {-, MonadState CheckOptData-})

deCheckOptM :: CheckOptM a -> ErrorT String (State CheckOptData) a
deCheckOptM (CheckOptM x) = x

newtype CheckOptM' t a = CheckOptM' (RestartT A.AST t CheckOptM a)
  deriving (Monad{-, MonadState (Route t A.AST)-})

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

liftRestartT :: Monad m => m a -> RestartT outer t m a
liftRestartT m = RestartT $ lift (m >>* Right)

elseError :: Bool -> String -> CheckOptM ()
elseError b err = CheckOptM $ if b then throwError err else return ()

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
      [Int] -> A.AST -> ErrorT String (State CheckOptData) ()
    doTree typeSet f route tr
      = do x <- traverse typeSet f (Just route) tr
           case x of
             Left (route', cont) -> do
               tr' <- get >>* ast
               doTree typeSet (\x -> cont x >> return ()) (maybe [] routeId route') tr'
             Right _ -> return ()

    -- | Given a TypeSet, a function to apply to everything of type a, a route
    -- location to begin at and an AST, transforms the tree.  If any restarts are
    -- requested, that is indicated in the return value
    traverse :: TypeSet -> (a -> RestartT A.AST a CheckOptM ()) -> Maybe [Int] -> A.AST ->
      ErrorT String (State CheckOptData)
        (Either (Maybe (Route a A.AST), a -> RestartT A.AST a CheckOptM A.AST) A.AST)
    traverse typeSet f route tr = (deCheckOptM $ flip runReaderT undefined (getRestartT $ flip
      evalStateT (case route of
        Just r -> Just r
        Nothing -> Just []) $ gen tr))
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
               Nothing -> lift $ apply typeSet f (y, route)
               Just targetRoute -> if targetRoute > routeId route then return y else do
                 put Nothing
                 lift $ apply typeSet f (y, route)
          )) x

    -- The return of this function is ignored.  All changes should be done in the
    -- state.
    apply :: TypeSet -> (a -> RestartT A.AST a CheckOptM ()) -> (a, Route a A.AST) -> RestartT A.AST a CheckOptM a
    apply typeSet f (x, route)
      = (RestartT $ ((local (const route) $ getRestartT (f x))))
        >> (liftRestartT (CheckOptM get) >>* ast >>* routeGet route)
        >>= gmapMForRoute typeSet (extTransformRoute baseTransformRoute $
              \(y, route') -> apply typeSet f (y, route @-> route'))


-- | For both of these functions I'm going to need to mark all analyses as no longer
-- valid, but more difficult will be to maintain the current position (if possible
-- -- should be in substitute, but not necessarily in replace) and continue.

-- | Substitutes the currently examined item for the given item, and continues
-- the traversal from the current point.  That is, the new item is transformed
-- again too.
substitute :: a -> CheckOptM' a a
substitute x = CheckOptM' $ RestartT $ ask >>= (\r -> return $ Left (Just r, return))

--replace :: t -> t -> CheckOptM' a ()
-- TODO think about what this means (replace everywhere, or just children?)

-- Restarts the current forAnyAST from the top of the tree, but keeps all changes
-- made thus far.
restartForAnyAST :: CheckOptM' a a
restartForAnyAST = CheckOptM' $ RestartT $ return $ Left (Nothing, return)

-- | Given a default value, followed by a function application with a
-- partial pattern match, gives back the default if the second parameter experiences
-- a pattern-match failure.
onlyIfPatternMatch :: a -> (b -> a) -> b -> IO a
onlyIfPatternMatch def f x = evaluate x >>= (\x' -> catchJust onlyPatternFail (evaluate
  $ f x') (const $ return def))
  where
    onlyPatternFail (PatternMatchFail {}) = Just ()
    onlyPatternFail _ = Nothing

--getParItems :: CheckOptM (ParItems ())
--getParItems = CheckOptM (\d -> Right (d, fromMaybe (generateParItems $ ast d) (parItems d)))

getParItems' :: CheckOptM' t (ParItems ())
getParItems' = undefined

generateParItems :: A.AST -> ParItems ()
generateParItems = undefined
