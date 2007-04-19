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
unnest p
    = parsToProcs p
       >>= removeFreeNames
       >>= removeNesting
       >>= removeNoSpecs

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

type NameMap = Map.Map String A.Name

-- | Get the set of free names within a block of code.
freeNamesIn :: Data t => t -> NameMap
freeNamesIn = doGeneric `extQ` doName `extQ` doProcess `extQ` doStructured `extQ` doValueProcess `extQ` doSpecType
  where
    doGeneric :: Data t => t -> NameMap
    doGeneric n = Map.unions $ gmapQ freeNamesIn n

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
    doSpec (A.Specification _ n st) child
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
removeFreeNames = doGeneric `extM` doSpecification `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapM removeFreeNames

    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification spec = case spec of
        A.Specification m n st@(A.Proc _ fs p) ->
          do
             ps <- get
             -- Figure out the free names. We only want to do this for channels
             -- and variables, and we don't want to do it for constants because
             -- they'll get pulled to the top level anyway.
             let allFreeNames = Map.elems $ freeNamesIn st
             let freeNames = [n | n <- allFreeNames,
                                  case A.nameType n of
                                    A.ChannelName -> True
                                    A.VariableName -> True
                                    _ -> False,
                                  not $ isConstName ps n]
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
             -- Add formals for each of the free names
             let newFs = [A.Formal am t n | (am, t, n) <- zip3 ams types newNames]
             p' <- removeFreeNames $ replaceNames (zip freeNames newNames) p
             let st' = A.Proc m (fs ++ newFs) p'
             let spec' = A.Specification m n st'
             -- Update the definition of the proc
             let nameDef = fromJust $ psLookupName ps n
             modify $ psDefineName n (nameDef { A.ndType = st' })
             -- Note that we should add extra arguments to calls of this proc
             -- when we find them
             let newAs = [case am of
                            A.Abbrev -> A.ActualVariable am t (A.Variable m n)
                            _ -> A.ActualExpression t (A.ExprVariable m (A.Variable m n))
                          | (am, n, t) <- zip3 ams freeNames types]
             case newAs of
               [] -> return ()
               _ -> modify $ (\ps -> ps { psAdditionalArgs = (A.nameName n, newAs) : psAdditionalArgs ps })
             return spec'
        _ -> doGeneric spec

    -- | Add the extra arguments we recorded when we saw the definition.
    doProcess :: A.Process -> PassM A.Process
    doProcess p@(A.ProcCall m n as)
        =  do st <- get
              case lookup (A.nameName n) (psAdditionalArgs st) of
                Just add -> doGeneric $ A.ProcCall m n (as ++ add)
                Nothing -> doGeneric p
    doProcess p = doGeneric p

-- | Pull nested declarations to the top level.
removeNesting :: A.Process -> PassM A.Process
removeNesting p
    =  do p' <- pullSpecs p
          applyPulled p'
  where
    pullSpecs :: Data t => t -> PassM t
    pullSpecs = doGeneric `extM` doSpecification

    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapM pullSpecs

    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification spec@(A.Specification m _ st)
        = do ps <- get
             if canPull ps st then
                 do spec' <- doGeneric spec
                    addPulled $ A.ProcSpec m spec'
                    return A.NoSpecification
               else doGeneric spec

    canPull :: ParseState -> A.SpecType -> Bool
    canPull _ (A.Proc _ _ _) = True
    canPull _ (A.DataType _ _) = True
    canPull _ (A.DataTypeRecord _ _ _) = True
    canPull _ (A.Protocol _ _) = True
    canPull _ (A.ProtocolCase _ _) = True
    canPull ps st = isConstSpecType ps st

-- | Remove specifications that have been turned into NoSpecifications.
removeNoSpecs :: Data t => t -> PassM t
removeNoSpecs = doGeneric `extM` doProcess `extM` doStructured `extM` doValueProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric n = gmapM removeNoSpecs n

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.ProcSpec _ A.NoSpecification p) = removeNoSpecs p
    doProcess p = doGeneric p

    doStructured :: A.Structured -> PassM A.Structured
    doStructured (A.Spec _ A.NoSpecification s) = removeNoSpecs s
    doStructured s = doGeneric s

    doValueProcess :: A.ValueProcess -> PassM A.ValueProcess
    doValueProcess (A.ValOfSpec _ A.NoSpecification vp) = removeNoSpecs vp
    doValueProcess vp = doGeneric vp
