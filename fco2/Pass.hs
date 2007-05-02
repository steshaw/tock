-- | Common definitions for passes over the AST.
module Pass where

import Control.Monad.Error
import Control.Monad.State
import Data.Generics
import Data.List
import System.IO

import qualified AST as A
import Errors
import Metadata
import ParseState
import PrettyShow

-- | The monad in which AST-mangling passes operate.
type PassM = ErrorT String (StateT ParseState IO)

instance Die PassM where
  die = throwError

-- | The type of an AST-mangling pass.
type Pass = A.Process -> PassM A.Process

-- | Compose a list of passes into a single pass.
runPasses :: [(String, Pass)] -> A.Process -> PassM A.Process
runPasses [] ast = return ast
runPasses ((s, p):ps) ast
    =  do debug $ "{{{ " ++ s
          progress $ "- " ++ s 
          ast' <- p ast
          debugAST ast'
          debug $ "}}}"
          runPasses ps ast'

-- | Print a message if above the given verbosity level.
verboseMessage :: (PSM m, MonadIO m) => Int -> String -> m ()
verboseMessage n s
    =  do ps <- get
          when (psVerboseLevel ps >= n) $
            liftIO $ hPutStrLn stderr s

-- | Print a warning message.
warn :: (PSM m, MonadIO m) => String -> m ()
warn = verboseMessage 0

-- | Print out any warnings stored.
showWarnings :: (PSM m, MonadIO m) => m ()
showWarnings
    =  do ps <- get
          sequence_ $ map warn (reverse $ psWarnings ps)
          put $ ps { psWarnings = [] }

-- | Print a progress message.
progress :: (PSM m, MonadIO m) => String -> m ()
progress = verboseMessage 1

-- | Print a debugging message.
debug :: (PSM m, MonadIO m) => String -> m ()
debug = verboseMessage 2

-- | Print a really verbose debugging message.
veryDebug :: (PSM m, MonadIO m) => String -> m ()
veryDebug = verboseMessage 3

-- | Dump the AST and parse state.
debugAST :: (PSM m, MonadIO m) => A.Process -> m ()
debugAST p
    =  do veryDebug $ "{{{ AST"
          veryDebug $ pshow p
          veryDebug $ "}}}"
          veryDebug $ "{{{ State"
          ps <- get
          veryDebug $ pshow ps
          veryDebug $ "}}}"

-- | Number lines in a piece of text.
numberLines :: String -> String
numberLines s
    = concat $ intersperse "\n" $ [show n ++ ": " ++ s
                                   | (n, s) <- zip [1..] (lines s)]

-- | Make a generic rule for a pass.
makeGeneric :: (Data t) => (forall s. Data s => s -> PassM s) -> t -> PassM t
makeGeneric top
    = (gmapM top)
        `extM` (return :: String -> PassM String)
        `extM` (return :: Meta -> PassM Meta)

