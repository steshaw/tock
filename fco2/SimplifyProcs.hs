-- | Simplify processes.
module SimplifyProcs (simplifyProcs) where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe

import qualified AST as A
import Metadata
import ParseState
import Types
import Pass

simplifyProcs :: A.Process -> PassM A.Process
simplifyProcs p
    = parsToProcs p

-- | Wrap the subprocesses of PARs in no-arg PROCs.
parsToProcs :: Data t => t -> PassM t
parsToProcs = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapM parsToProcs

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Par m pm ps)
        =  do ps' <- mapM parsToProcs ps
              procs <- mapM (makeNonceProc m) ps'
              let calls = [A.ProcSpec m s (A.ProcCall m n []) | s@(A.Specification m n _) <- procs]
              return $ A.Par m pm calls
    doProcess (A.ParRep m pm rep p)
        =  do p' <- parsToProcs p
              rep' <- parsToProcs rep
              s@(A.Specification _ n _) <- makeNonceProc m p'
              let call = A.ProcSpec m s (A.ProcCall m n [])
              return $ A.ParRep m pm rep' call
    doProcess p = doGeneric p

