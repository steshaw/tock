-- | Flatten nested declarations.
module Unnest (unnest) where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe

import qualified AST as A
import CompState
import EvalConstants
import Metadata
import Pass
import Types

unnest :: A.Process -> PassM A.Process
unnest = runPasses passes
  where
    passes =
      [ ("Convert free names to arguments", removeFreeNames)
      , ("Pull nested definitions to top level", removeNesting)
      ]

type NameMap = Map.Map String A.Name

-- | Get the set of free names within a block of code.
freeNamesIn :: Data t => t -> NameMap
freeNamesIn = doGeneric
                `extQ` (ignore :: String -> NameMap)
                `extQ` (ignore :: Meta -> NameMap)
                `extQ` doName `extQ` doStructured `extQ` doSpecType
  where
    doGeneric :: Data t => t -> NameMap
    doGeneric n = Map.unions $ gmapQ freeNamesIn n

    ignore :: t -> NameMap
    ignore s = Map.empty

    doName :: A.Name -> NameMap
    doName n = Map.singleton (A.nameName n) n

    doStructured :: A.Structured -> NameMap
    doStructured (A.Rep _ rep s) = doRep rep s
    doStructured (A.Spec _ spec s) = doSpec spec s
    doStructured s = doGeneric s

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
    doSpecType (A.Proc _ _ fs p) = Map.difference (freeNamesIn p) (freeNamesIn fs)
    doSpecType (A.Function _ _ _ fs vp) = Map.difference (freeNamesIn vp) (freeNamesIn fs)
    doSpecType st = doGeneric st

-- | Replace names.
replaceNames :: Data t => [(A.Name, A.Name)] -> t -> t
replaceNames map p = everywhere (mkT doName
                                   `extT` (id :: String -> String)
                                   `extT` (id :: Meta -> Meta)
                                ) p
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
    doGeneric = makeGeneric removeFreeNames

    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification spec = case spec of
        A.Specification m n st@(A.Proc _ _ _ _) ->
          do st'@(A.Proc mp sm fs p) <- removeFreeNames st

             -- If this is the top-level process, we shouldn't add new args --
             -- we know it's not going to be moved by removeNesting, so anything
             -- that it had in scope originally will still be in scope.
             ps <- get
             let isTLP = (snd $ head $ csMainLocals ps) == n

             -- Figure out the free names.
             let freeNames' = if isTLP then [] else Map.elems $ freeNamesIn st'
             let freeNames'' = [n | n <- freeNames',
                                    case A.nameType n of
                                      A.ChannelName -> True
                                      A.PortName -> True
                                      A.TimerName -> True
                                      A.VariableName -> True
                                      _ -> False]

             -- Don't bother with constants -- they get pulled up anyway.
             freeNames <- filterM (liftM not . isConstantName) freeNames''
             types <- mapM typeOfName freeNames
             origAMs <- mapM abbrevModeOfName freeNames
             let ams = map makeAbbrevAM origAMs

             -- Generate and define new names to replace them with
             newNamesS <- sequence [makeNonce (A.nameName n) | n <- freeNames]
             let newNames = [on { A.nameName = nn } | (on, nn) <- zip freeNames newNamesS]
             onds <- mapM lookupName freeNames
             sequence_ [defineName nn (ond { A.ndName = A.nameName nn,
                                             A.ndAbbrevMode = am })
                        | (ond, nn, am) <- zip3 onds newNames ams]

             -- Add formals for each of the free names
             let newFs = [A.Formal am t n | (am, t, n) <- zip3 ams types newNames]
             let st'' = A.Proc mp sm (fs ++ newFs) $ replaceNames (zip freeNames newNames) p
             let spec' = A.Specification m n st''

             -- Update the definition of the proc
             nameDef <- lookupName n
             defineName n (nameDef { A.ndType = st'' })

             -- Note that we should add extra arguments to calls of this proc
             -- when we find them
             let newAs = [case am of
                            A.Abbrev -> A.ActualVariable am t (A.Variable m n)
                            _ -> A.ActualExpression t (A.ExprVariable m (A.Variable m n))
                          | (am, n, t) <- zip3 ams freeNames types]
             debug $ "removeFreeNames: " ++ show n ++ " has new args " ++ show newAs
             when (newAs /= []) $
               modify $ (\ps -> ps { csAdditionalArgs = Map.insert (A.nameName n) newAs (csAdditionalArgs ps) })

             return spec'
        _ -> doGeneric spec

    -- | Add the extra arguments we recorded when we saw the definition.
    doProcess :: A.Process -> PassM A.Process
    doProcess p@(A.ProcCall m n as)
        =  do st <- get
              case Map.lookup (A.nameName n) (csAdditionalArgs st) of
                Just add -> doGeneric $ A.ProcCall m n (as ++ add)
                Nothing -> doGeneric p
    doProcess p = doGeneric p

-- | Pull nested declarations to the top level.
removeNesting :: A.Process -> PassM A.Process
removeNesting p
    =  do pushPullContext
          p' <- pullSpecs p
          s <- applyPulled $ A.OnlyP emptyMeta p'
          popPullContext
          return $ A.Seq emptyMeta s
  where
    pullSpecs :: Data t => t -> PassM t
    pullSpecs = doGeneric `extM` doStructured

    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric pullSpecs

    doStructured :: A.Structured -> PassM A.Structured
    doStructured s@(A.Spec m spec@(A.Specification _ n st) subS)
        = do isConst <- isConstantName n
             if isConst || canPull st then
                 do debug $ "removeNesting: pulling up " ++ show n
                    spec' <- doGeneric spec
                    addPulled $ A.Spec m spec'
                    doStructured subS
               else doGeneric s
    doStructured s = doGeneric s

    canPull :: A.SpecType -> Bool
    canPull (A.Proc _ _ _ _) = True
    canPull (A.RecordType _ _ _) = True
    canPull (A.Protocol _ _) = True
    canPull (A.ProtocolCase _ _) = True
    canPull _ = False

