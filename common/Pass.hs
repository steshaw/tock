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
import Control.Monad.State
import Data.Generics
import Data.List
import System.IO

import qualified AST as A
import CompState
import Errors
import Metadata
import PrettyShow
import TreeUtil

-- | The monad in which AST-mangling passes operate.
type PassM = ErrorT ErrorReport (StateT CompState IO)

instance Die PassM where
  dieReport = throwError

-- | The type of an AST-mangling pass.
type Pass = A.Structured -> PassM A.Structured

-- | Compose a list of passes into a single pass.
runPasses :: [(String, Pass)] -> Pass
runPasses [] ast = return ast
runPasses ((s, p):ps) ast
    =  do debug $ "{{{ " ++ s
          progress $ "- " ++ s 
          ast' <- p ast
          debugAST ast'
          debug $ "}}}"
          runPasses ps ast'

-- | Print a message if above the given verbosity level.
verboseMessage :: (CSM m, MonadIO m) => Int -> String -> m ()
verboseMessage n s
    =  do ps <- get
          when (csVerboseLevel ps >= n) $
            liftIO $ hPutStrLn stderr s

-- | Print a warning message.
warn :: (CSM m, MonadIO m) => String -> m ()
warn = verboseMessage 0

-- | Print out any warnings stored.
showWarnings :: (CSM m, MonadIO m) => m ()
showWarnings
    =  do ps <- get
          sequence_ $ map warn (reverse $ csWarnings ps)
          put $ ps { csWarnings = [] }

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

excludeConstr :: Data a => [Constr] -> a -> PassM a
excludeConstr cons x 
  = if null items then return x else dieInternal (Nothing, "Excluded item still remains in source tree: " ++ (show $ head items) ++ " tree is: " ++ pshow x)
      where
        items = checkTreeForConstr cons x
