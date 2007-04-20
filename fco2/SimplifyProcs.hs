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
       >>= removeParAssign

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

-- | Turn parallel assignment into multiple single assignments.
removeParAssign :: Data t => t -> PassM t
removeParAssign = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapM removeParAssign

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Assign m vs@(_:_:_) (A.ExpressionList _ es))
        =  do ps <- get
              let ts = [fromJust $ typeOfVariable ps v | v <- vs]
              specs <- sequence [makeNonceVariable "assign_temp" m t A.VariableName A.Original | t <- ts]
              let temps = [A.Variable m n | A.Specification _ n _ <- specs]
              let first = [A.Assign m [v] (A.ExpressionList m [e]) | (v, e) <- zip temps es]
              let second = [A.Assign m [v] (A.ExpressionList m [A.ExprVariable m v']) | (v, v') <- zip vs temps]
              return $ foldl (\p s -> A.ProcSpec m s p) (A.Seq m $ first ++ second) specs
    doProcess p = doGeneric p

