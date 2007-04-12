-- | Simplify expressions in the AST.
module SimplifyExprs (simplifyExprs) where

import Control.Monad.State
import Data.Generics

import qualified AST as A
import Metadata
import ParseState
import Types
import Pass

simplifyExprs :: A.Process -> PassM A.Process
simplifyExprs = pullUp

pullUp :: Data t => t -> PassM t
pullUp = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapM pullUp

    doProcess :: A.Process -> PassM A.Process
    doProcess p
        =  do p' <- doGeneric p
              liftIO $ putStrLn $ "looking at process"
              return p'

