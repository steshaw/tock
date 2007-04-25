-- | Common definitions for passes over the AST.
module Pass where

import Control.Monad.Error
import Control.Monad.State
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

-- | Run a pass, dying with the appropriate error if it fails.
runPass :: Pass -> A.Process -> ParseState -> IO (A.Process, ParseState)
runPass pass ast st
    =  do (v, ps) <- runStateT (runErrorT (pass ast)) st
          case v of
            Left e -> dieIO e
            Right r -> return (r, ps)

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

verboseMessage :: Int -> String -> PassM ()
verboseMessage n s
    =  do ps <- get
          liftIO $ verboseMessageIO n ps s

verboseMessageIO :: Int -> ParseState -> String -> IO ()
verboseMessageIO n ps s = when (psVerboseLevel ps >= n) $ hPutStrLn stderr s

-- | Print a progress message if appropriate.
progress :: String -> PassM ()
progress = verboseMessage 1

-- | Print a progress message if appropriate (in the IO monad).
progressIO :: ParseState -> String -> IO ()
progressIO = verboseMessageIO 1

-- | Print a debugging message if appropriate.
debug :: String -> PassM ()
debug = verboseMessage 2

-- | Print a debugging message if appropriate (in the IO monad).
debugIO :: ParseState -> String -> IO ()
debugIO = verboseMessageIO 2

-- | Dump the AST and parse state if appropriate.
debugAST :: A.Process -> PassM ()
debugAST p
    =  do ps <- get
          liftIO $ debugASTIO ps p

-- | Dump the AST and parse state if appropriate (in the IO monad).
debugASTIO :: ParseState -> A.Process -> IO ()
debugASTIO ps p
    =  do debugIO ps $ "{{{ AST"
          debugIO ps $ pshow p
          debugIO ps $ "}}}"
          debugIO ps $ "{{{ State"
          debugIO ps $ pshow ps
          debugIO ps $ "}}}"

