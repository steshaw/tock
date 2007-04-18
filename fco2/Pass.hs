-- | Common definitions for passes over the AST.
module Pass where

import Control.Monad.State
import System.IO

import qualified AST as A
import ParseState

type PassM a = StateT ParseState IO a

type Pass = A.Process -> PassM A.Process

runPass :: Pass -> A.Process -> ParseState -> IO (A.Process, ParseState)
runPass pass ast st = runStateT (pass ast) st

runPasses :: (String -> IO ()) -> [(String, Pass)] -> A.Process -> PassM A.Process
runPasses _ [] ast = return ast
runPasses progress ((s, p):ps) ast
    =  do liftIO $ progress $ "{{{ " ++ s
          ast' <- p ast
          liftIO $ progress $ "}}}"
          ast'' <- runPasses progress ps ast'
          return ast''

debug :: String -> PassM ()
debug s = liftIO $ hPutStrLn stderr s

