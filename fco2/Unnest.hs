-- | Flatten nested declarations.
module Unnest where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe

import qualified AST as A
import Metadata
import ParseState
import Types

type UnM a = StateT ParseState IO a

-- | Generate and define a no-arg wrapper PROC around a process.
makeNonceProc :: Meta -> A.Process -> UnM A.Specification
makeNonceProc m p
    =  do ns <- makeNonce "wrapper_proc"
          let n = A.Name m A.ProcName ns
          let st = A.Proc m [] p
          let nd = A.NameDef {
                     A.ndMeta = m,
                     A.ndName = ns,
                     A.ndOrigName = ns,
                     A.ndNameType = A.ProcName,
                     A.ndType = st,
                     A.ndAbbrevMode = A.Abbrev
                   }
          modify $ psDefineName n nd
          return (n, st)

unnest :: ParseState -> A.Process -> IO (ParseState, A.Process)
unnest ps ast
    =  do (ast', ps') <- runStateT (parsToProcs ast) ps
          (ast'', ps'') <- runStateT (removeFreeNames ast') ps'
          (ast''', ps''') <- runStateT (removeNesting ast'') ps''
          return (ps''', ast''')

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

type NameMap = Map.Map String A.Name

-- | Get the set of free names within a block of code.
freeNamesIn :: Data t => t -> NameMap
freeNamesIn = doGeneric `extQ` doName `extQ` doProcess `extQ` doStructured `extQ` doValueProcess `extQ` doSpecType
  where
    doGeneric :: Data t => t -> NameMap
    doGeneric n = Map.unions $ gmapQ freeNamesIn n

    -- FIXME This won't do the right thing with tags.
    doName :: A.Name -> NameMap
    doName n = Map.singleton (A.nameName n) n

    doProcess :: A.Process -> NameMap
    doProcess (A.ProcSpec _ spec p) = doSpec spec p
    doProcess (A.SeqRep _ rep p) = doRep rep p
    doProcess (A.ParRep _ _ rep p) = doRep rep p
    doProcess p = doGeneric p

    doStructured :: A.Structured -> NameMap
    doStructured (A.Rep _ rep s) = doRep rep s
    doStructured (A.Spec _ spec s) = doSpec spec s
    doStructured s = doGeneric s

    doValueProcess :: A.ValueProcess -> NameMap
    doValueProcess (A.ValOfSpec _ spec vp) = doSpec spec vp
    doValueProcess vp = doGeneric vp

    doSpec :: Data t => A.Specification -> t -> NameMap
    doSpec (n, st) child
        = Map.union fns $ Map.delete (A.nameName n) $ freeNamesIn child
      where
        fns = freeNamesIn st

    doRep :: Data t => A.Replicator -> t -> NameMap
    doRep rep child
        = Map.union fns $ Map.delete (A.nameName repName) $ freeNamesIn child
      where
        (repName, fns) = case rep of
          A.For _ n b c -> (n, Map.union (freeNamesIn b) (freeNamesIn c))

    doSpecType :: A.SpecType -> NameMap
    doSpecType (A.Proc _ fs p) = Map.difference (freeNamesIn p) (freeNamesIn fs)
    doSpecType (A.Function _ _ fs vp) = Map.difference (freeNamesIn vp) (freeNamesIn fs)
    doSpecType st = doGeneric st

-- | Turn free names in PROCs into arguments.
removeFreeNames :: Data t => t -> UnM t
removeFreeNames = doGeneric `extM` doProcess `extM` doStructured `extM` doValueProcess
  where
    doGeneric :: Data t => t -> UnM t
    doGeneric = gmapM removeFreeNames

    doProcess :: A.Process -> UnM A.Process
    doProcess (A.ProcSpec m spec p)
        =  do (spec', p') <- doSpec m spec p
              return $ A.ProcSpec m spec' p'
    doProcess p = doGeneric p

    doStructured :: A.Structured -> UnM A.Structured
    doStructured (A.Spec m spec s)
        =  do (spec', s') <- doSpec m spec s
              return $ A.Spec m spec' s'
    doStructured s = doGeneric s

    doValueProcess :: A.ValueProcess -> UnM A.ValueProcess
    doValueProcess (A.ValOfSpec m spec vp)
        =  do (spec', vp') <- doSpec m spec vp
              return $ A.ValOfSpec m spec' vp'
    doValueProcess vp = doGeneric vp

    addToCalls :: Data t => A.Name -> [A.Actual] -> t -> t
    addToCalls matchN newAs = everywhere (mkT atcProc)
      where
        atcProc :: A.Process -> A.Process
        atcProc p@(A.ProcCall m n as)
            = if sameName n matchN then A.ProcCall m n (as ++ newAs) else p
        atcProc p = p

    doSpec :: Data t => Meta -> A.Specification -> t -> UnM (A.Specification, t)
    doSpec m spec child = case spec of
        (n, st@(A.Proc m fs p)) ->
          do
             -- Figure out the free names
             let allFreeNames = Map.elems $ freeNamesIn st
             let freeNames = [n | n <- allFreeNames,
                                  case A.nameType n of
                                    A.ChannelName -> True
                                    A.VariableName -> True
                                    _ -> False]
             ps <- get
             let types = [fromJust $ typeOfName ps n | n <- freeNames]
             -- Add formals for each of the free names
             let newFs = [A.Formal A.Abbrev t n | (t, n) <- zip types freeNames]
             p' <- removeFreeNames p
             let spec' = (n, A.Proc m (fs ++ newFs) p')
             -- Add extra arguments to calls of this proc
             let newAs = [case A.nameType n of
                            A.ChannelName -> A.ActualChannel (A.Channel m n)
                            A.VariableName -> A.ActualExpression (A.ExprVariable m (A.Variable m n))
                          | (t, n) <- zip types freeNames]
             child' <- removeFreeNames (addToCalls n newAs child)
             return (spec', child')
        _ ->
          do spec' <- removeFreeNames spec
             child' <- removeFreeNames child
             return (spec', child')

-- | Pull nested declarations to the top level.
removeNesting :: A.Process -> UnM A.Process
removeNesting p
    =  do p' <- pullSpecs p
          st <- get
          let pulled = psPulledSpecs st
          put $ st { psPulledSpecs = [] }
          return $ foldl (\p (m, spec) -> A.ProcSpec m spec p) p' pulled
  where
    pullSpecs :: Data t => t -> UnM t
    pullSpecs = doGeneric `extM` doProcess `extM` doStructured `extM` doValueProcess

    doGeneric :: Data t => t -> UnM t
    doGeneric = gmapM pullSpecs

    doProcess :: A.Process -> UnM A.Process
    doProcess orig@(A.ProcSpec m spec p) = doSpec orig m spec p
    doProcess p = doGeneric p

    doStructured :: A.Structured -> UnM A.Structured
    doStructured orig@(A.Spec m spec s) = doSpec orig m spec s
    doStructured s = doGeneric s

    doValueProcess :: A.ValueProcess -> UnM A.ValueProcess
    doValueProcess orig@(A.ValOfSpec m spec vp) = doSpec orig m spec vp
    doValueProcess vp = doGeneric vp

    doSpec :: Data t => t -> Meta -> A.Specification -> t -> UnM t
    doSpec orig m spec@(_, st) child
        = if canPull st then
            do spec' <- pullSpecs spec
               modify $ (\ps -> ps { psPulledSpecs = (m, spec') : psPulledSpecs ps })
               child' <- pullSpecs child
               return child'
          else doGeneric orig

    canPull :: A.SpecType -> Bool
    canPull (A.Proc _ _ _) = True
    canPull (A.DataType _ _) = True
    canPull (A.DataTypeRecord _ _ _) = True
    canPull (A.Protocol _ _) = True
    canPull (A.ProtocolCase _ _) = True
    -- FIXME: Should pull up constant expressions too
    canPull _ = False

