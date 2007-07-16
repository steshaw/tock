-- | Simplify processes.
module SimplifyProcs (simplifyProcs) where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe

import qualified AST as A
import CompState
import Metadata
import Types
import Pass

simplifyProcs :: A.Process -> PassM A.Process
simplifyProcs = runPasses passes
  where
    passes =
      [ ("Wrap PAR subprocesses in PROCs", parsToProcs)
      , ("Remove parallel assignment", removeParAssign)
      ]

-- | Wrap the subprocesses of PARs in no-arg PROCs.
parsToProcs :: Data t => t -> PassM t
parsToProcs = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric parsToProcs

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Par m pm s)
        =  do s' <- doStructured s
              return $ A.Par m pm s'
    doProcess p = doGeneric p

    -- FIXME This should be generic and in Pass.
    doStructured :: A.Structured -> PassM A.Structured
    doStructured (A.Rep m r s)
        =  do r' <- parsToProcs r
              s' <- doStructured s
              return $ A.Rep m r' s'
    doStructured (A.Spec m spec s)
        =  do spec' <- parsToProcs spec
              s' <- doStructured s
              return $ A.Spec m spec' s'
    doStructured (A.ProcThen m p s)
        =  do p' <- parsToProcs p
              s' <- doStructured s
              return $ A.ProcThen m p' s'
    doStructured (A.OnlyP m p)
        =  do p' <- parsToProcs p
              s@(A.Specification _ n _) <- makeNonceProc m p'
              return $ A.Spec m s (A.OnlyP m (A.ProcCall m n []))
    doStructured (A.Several m ss)
        = liftM (A.Several m) $ mapM doStructured ss

-- | Turn parallel assignment into multiple single assignments through temporaries.
removeParAssign :: Data t => t -> PassM t
removeParAssign = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric removeParAssign

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Assign m vs@(_:_:_) (A.ExpressionList _ es))
        =  do ts <- mapM typeOfVariable vs
              specs <- sequence [makeNonceVariable "assign_temp" m t A.VariableName A.Original | t <- ts]
              let temps = [A.Variable m n | A.Specification _ n _ <- specs]
              let first = [A.Assign m [v] (A.ExpressionList m [e]) | (v, e) <- zip temps es]
              let second = [A.Assign m [v] (A.ExpressionList m [A.ExprVariable m v']) | (v, v') <- zip vs temps]
              return $ A.Seq m $ foldl (\s spec -> A.Spec m spec s) (A.Several m (map (A.OnlyP m) (first ++ second))) specs
    doProcess p = doGeneric p

