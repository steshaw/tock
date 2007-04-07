-- | Flatten nested declarations.
module Unnest where

import Control.Monad.State
import Data.Generics

import qualified AST as A
import Metadata
import ParseState
import Types

type UnM a = StateT ParseState IO a

-- | Generate and define a no-arg wrapper PROC around a process.
makeNonceProc :: Meta -> A.Process -> UnM A.Specification
makeNonceProc m p
    =  do ns <- makeNonce
          let n = A.Name m A.ProcName ns
          let st = A.Proc m [] p
          let nd = A.NameDef {
                     A.ndMeta = m,
                     A.ndName = ns,
                     A.ndOrigName = "PAR branch",
                     A.ndType = st,
                     A.ndAbbrevMode = A.Abbrev
                   }
          modify $ psDefineName n nd
          return (n, st)

unnest :: ParseState -> A.Process -> IO (ParseState, A.Process)
unnest ps ast
    =  do (ast', ps') <- runStateT (parsToProcs ast) ps
          (ast'', ps'') <- runStateT (removeNesting ast') ps'
          return (ps'', ast'')

-- | Wrap the subprocesses of PARs in no-arg PROCs.
parsToProcs :: Data t => t -> UnM t
parsToProcs = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> UnM t
    doGeneric = gmapM parsToProcs

    doProcess :: A.Process -> UnM A.Process
    doProcess (A.Par m pm ps)
        =  do ps' <- mapM parsToProcs ps
              procs <- mapM (makeNonceProc m) ps'
              let calls = [A.ProcSpec m s (A.ProcCall m n []) | s@(n, _) <- procs]
              return $ A.Par m pm calls
    doProcess (A.ParRep m pm rep p)
        =  do p' <- parsToProcs p
              rep' <- parsToProcs rep
              s@(n, _) <- makeNonceProc m p'
              let call = A.ProcSpec m s (A.ProcCall m n [])
              return $ A.ParRep m pm rep' call
    doProcess p = doGeneric p

-- | Pull nested declarations to the top level.
removeNesting :: Data t => t -> UnM t
removeNesting p = return p

