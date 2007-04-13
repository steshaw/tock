-- | Flatten nested declarations.
module Unnest (unnest) where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe

import qualified AST as A
import Metadata
import ParseState
import Types
import Pass

unnest :: A.Process -> PassM A.Process
unnest p = parsToProcs p >>= removeFreeNames >>= removeNesting

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

-- | Replace names.
replaceNames :: Data t => [(A.Name, A.Name)] -> t -> t
replaceNames map p = everywhere (mkT $ doName) p
  where
    smap = [(A.nameName f, t) | (f, t) <- map]

    doName :: A.Name -> A.Name
    doName n
        = case lookup (A.nameName n) smap of
            Just n' -> n'
            Nothing -> n

-- | Turn free names in PROCs into arguments.
removeFreeNames :: Data t => t -> PassM t
removeFreeNames = doGeneric `extM` doProcess `extM` doStructured `extM` doValueProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapM removeFreeNames

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.ProcSpec m spec p)
        =  do (spec', p') <- doSpec m spec p
              return $ A.ProcSpec m spec' p'
    doProcess p = doGeneric p

    doStructured :: A.Structured -> PassM A.Structured
    doStructured (A.Spec m spec s)
        =  do (spec', s') <- doSpec m spec s
              return $ A.Spec m spec' s'
    doStructured s = doGeneric s

    doValueProcess :: A.ValueProcess -> PassM A.ValueProcess
    doValueProcess (A.ValOfSpec m spec vp)
        =  do (spec', vp') <- doSpec m spec vp
              return $ A.ValOfSpec m spec' vp'
    doValueProcess vp = doGeneric vp

    addToCalls :: Data t => A.Name -> [A.Actual] -> t -> t
    addToCalls matchN newAs = everywhere (mkT atcProc)
      where
        atcProc :: A.Process -> A.Process
        atcProc p@(A.ProcCall m n as)
            = if n == matchN then A.ProcCall m n (as ++ newAs) else p
        atcProc p = p

    doSpec :: Data t => Meta -> A.Specification -> t -> PassM (A.Specification, t)
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
             let ams = [case fromJust $ abbrevModeOfName ps n of
                          A.Original -> A.Abbrev
                          t -> t
                        | n <- freeNames]
             -- Generate and define new names to replace them with
             newNamesS <- sequence [makeNonce (A.nameName n) | n <- freeNames]
             let newNames = [on { A.nameName = nn } | (on, nn) <- zip freeNames newNamesS]
             sequence_ [let ond = fromJust $ psLookupName ps on
                          in modify $ psDefineName nn (ond { A.ndName = A.nameName nn,
                                                             A.ndAbbrevMode = am })
                        | (on, nn, am) <- zip3 freeNames newNames ams]
             ps' <- get
             -- Add formals for each of the free names
             let newFs = [A.Formal am t n | (am, t, n) <- zip3 ams types newNames]
             p' <- removeFreeNames $ replaceNames (zip freeNames newNames) p
             let st' = A.Proc m (fs ++ newFs) p'
             let spec' = (n, st')
             -- Update the definition of the proc
             let nameDef = fromJust $ psLookupName ps n
             modify $ psDefineName n (nameDef { A.ndType = st' })
             -- Add extra arguments to calls of this proc
             let newAs = [case am of
                            A.Abbrev -> A.ActualVariable am t (A.Variable m n)
                            _ -> A.ActualExpression t (A.ExprVariable m (A.Variable m n))
                          | (am, n, t) <- zip3 ams freeNames types]
             child' <- removeFreeNames (addToCalls n newAs child)
             return (spec', child')
        _ ->
          do spec' <- removeFreeNames spec
             child' <- removeFreeNames child
             return (spec', child')

-- | Pull nested declarations to the top level.
removeNesting :: A.Process -> PassM A.Process
removeNesting p
    =  do p' <- pullSpecs p
          applyPulled p'
  where
    pullSpecs :: Data t => t -> PassM t
    pullSpecs = doGeneric `extM` doProcess `extM` doStructured `extM` doValueProcess

    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapM pullSpecs

    doProcess :: A.Process -> PassM A.Process
    doProcess orig@(A.ProcSpec m spec p) = doSpec orig m spec p
    doProcess p = doGeneric p

    doStructured :: A.Structured -> PassM A.Structured
    doStructured orig@(A.Spec m spec s) = doSpec orig m spec s
    doStructured s = doGeneric s

    doValueProcess :: A.ValueProcess -> PassM A.ValueProcess
    doValueProcess orig@(A.ValOfSpec m spec vp) = doSpec orig m spec vp
    doValueProcess vp = doGeneric vp

    doSpec :: Data t => t -> Meta -> A.Specification -> t -> PassM t
    doSpec orig m spec@(_, st) child
        = if canPull st then
            do spec' <- pullSpecs spec
               addPulled $ A.ProcSpec m spec'
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

