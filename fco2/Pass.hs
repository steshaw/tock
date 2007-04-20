-- | Common definitions for passes over the AST.
module Pass where

import Control.Monad.State
import System.IO

import qualified AST as A
import ParseState
import PrettyShow

type PassM a = StateT ParseState IO a

type Pass = A.Process -> PassM A.Process

runPass :: Pass -> A.Process -> ParseState -> IO (A.Process, ParseState)
runPass pass ast st = runStateT (pass ast) st

runPasses :: [(String, Pass)] -> A.Process -> PassM A.Process
runPasses [] ast = return ast
runPasses ((s, p):ps) ast
    =  do debug $ "{{{ " ++ s
          progress $ "- " ++ s 
          ast' <- p ast
          debugAST ast'
          debug $ "}}}"
          runPasses ps ast'

progress :: String -> PassM ()
progress s
    =  do ps <- get
          liftIO $ progressIO ps s

progressIO :: ParseState -> String -> IO ()
progressIO ps s = when (Verbose `elem` psFlags ps) $ hPutStrLn stderr s

debug :: String -> PassM ()
debug s
    =  do ps <- get
          liftIO $ debugIO ps s

debugIO :: ParseState -> String -> IO ()
debugIO ps s = when (Debug `elem` psFlags ps) $ hPutStrLn stderr s

debugASTIO :: ParseState -> A.Process -> IO ()
debugASTIO ps p
    =  do debugIO ps $ "{{{ AST"
          debugIO ps $ pshow p
          debugIO ps $ "}}}"
          debugIO ps $ "{{{ State"
          debugIO ps $ pshow ps
          debugIO ps $ "}}}"

debugAST :: A.Process -> PassM ()
debugAST p
    =  do ps <- get
          liftIO $ debugASTIO ps p

