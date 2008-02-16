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

-- | Common definitions for passes over the AST.
module Pass where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Generics
import Data.List
import qualified Data.Set as Set
import System.IO

import qualified AST as A
import CompState
import Errors
import Metadata
import PrettyShow
import TreeUtils

-- | The monad in which AST-mangling passes operate.
type PassM = ErrorT ErrorReport (StateT CompState (WriterT [WarningReport]  IO))
type PassMR = ErrorT ErrorReport (ReaderT CompState (WriterT [WarningReport]  IO))

instance Die PassM where
  dieReport = throwError

instance Die PassMR where
  dieReport = throwError
  
instance Warn PassM where
  warnReport w = tell [w]

instance Warn PassMR where
  warnReport w = tell [w]

-- | The type of an AST-mangling pass.
data Monad m => Pass_ m = Pass {
  passCode :: A.AST -> m A.AST
 ,passName :: String 
 ,passPre :: Set.Set Property
 ,passPost :: Set.Set Property
 ,passEnabled :: CompState -> Bool
}
  
type Pass = Pass_ PassM
type PassR = Pass_ PassMR

data Property = Property {
  propName :: String
 ,propCheck :: A.AST -> PassMR ()
}

instance Eq Property where
  x == y = propName x == propName y
  
instance Ord Property where
  compare x y = compare (propName x) (propName y)

runPassR :: (A.AST -> PassMR A.AST) -> (A.AST -> PassM A.AST)
runPassR p t 
           = do st <- get
                (r,w) <- liftIO $ runWriterT $ runReaderT (runErrorT (p t)) st
                case r of
                  Left err -> throwError err
                  Right result -> tell w >> return result

makePasses :: [(String, A.AST -> PassM A.AST)] -> [Pass]
makePasses = map (\(s, p) -> Pass p s Set.empty Set.empty (const True))

makePasses' :: (CompState -> Bool) -> [(String, A.AST -> PassM A.AST)] -> [Pass]
makePasses' f = map (\(s, p) -> Pass p s Set.empty Set.empty f)

-- | Compose a list of passes into a single pass.
-- TODO this needs to examine dependencies rather than running them in order!

runPasses :: [Pass] -> (A.AST -> PassM A.AST)
runPasses [] ast = return ast
runPasses (p:ps) ast
    =  do debug $ "{{{ " ++ passName p
          progress $ "- " ++ passName p
          ast' <- passCode p ast
          debugAST ast'
          debug $ "}}}"
          runPasses ps ast'


-- | Print a message if above the given verbosity level.
verboseMessage :: (CSM m, MonadIO m) => Int -> String -> m ()
verboseMessage n s
    =  do ps <- get
          when (csVerboseLevel ps >= n) $
            liftIO $ hPutStrLn stderr s

-- | Print a progress message.
progress :: (CSM m, MonadIO m) => String -> m ()
progress = verboseMessage 1

-- | Print a debugging message.
debug :: (CSM m, MonadIO m) => String -> m ()
debug = verboseMessage 2

-- | Print a really verbose debugging message.
veryDebug :: (CSM m, MonadIO m) => String -> m ()
veryDebug = verboseMessage 3

-- | Dump the AST and parse state.
debugAST :: (CSM m, MonadIO m, Data t) => t -> m ()
debugAST p
    =  do veryDebug $ "{{{ AST"
          veryDebug $ pshow p
          veryDebug $ "}}}"
          veryDebug $ "{{{ State"
          ps <- get
          veryDebug $ pshow ps
          veryDebug $ "}}}"

-- | Make a generic rule for a pass.
makeGeneric :: (Data t) => (forall s. Data s => s -> PassM s) -> t -> PassM t
makeGeneric top
    = (gmapM top)
        `extM` (return :: String -> PassM String)
        `extM` (return :: Meta -> PassM Meta)

excludeConstr :: (Data a, CSMR m) => [Constr] -> a -> m a
excludeConstr cons x 
  = if null items then return x else dieInternal (Nothing, "Excluded item still remains in source tree: " ++ (show $ head items) ++ " tree is: " ++ pshow x)
      where
        items = checkTreeForConstr cons x

mk1M :: (Monad m, Data a, Typeable1 t) => (forall d . Data d => t d -> m (t d)) -> a -> m a
mk1M = ext1M return
