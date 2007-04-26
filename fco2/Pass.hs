-- | Common definitions for passes over the AST.
module Pass where

import Control.Monad.Error
import Control.Monad.State
import Data.List
import System.IO

import qualified AST as A
import Errors
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

-- | Print a progress message.
progress :: (PSM m, MonadIO m) => String -> m ()
progress = verboseMessage 1

-- | Print a debugging message.
debug :: (PSM m, MonadIO m) => String -> m ()
debug = verboseMessage 2

-- | Dump the AST and parse state.
debugAST :: (PSM m, MonadIO m) => A.Process -> m ()
debugAST p
    =  do debug $ "{{{ AST"
          debug $ pshow p
          debug $ "}}}"
          debug $ "{{{ State"
          ps <- get
          debug $ pshow ps
          debug $ "}}}"

-- | Number lines in a piece of text.
numberLines :: String -> String
numberLines s
    = concat $ intersperse "\n" $ [show n ++ ": " ++ s
                                   | (n, s) <- zip [1..] (lines s)]

