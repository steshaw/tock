-- | Common definitions for passes over the AST.
module Pass where

import Control.Monad.State

import qualified AST as A
import ParseState

type PassM a = StateT ParseState IO a

type Pass = A.Process -> PassM A.Process

runPass :: Pass -> A.Process -> ParseState -> IO (A.Process, ParseState)
runPass pass ast st = runStateT (pass ast) st

runPasses :: [(String, Pass)] -> A.Process -> PassM A.Process
runPasses [] ast = return ast
runPasses ((s, p):ps) ast
    =  do liftIO $ putStrLn $ "{{{ " ++ s
          ast' <- p ast
          liftIO $ putStrLn $ "}}}"
          ast'' <- runPasses ps ast'
          return ast''

