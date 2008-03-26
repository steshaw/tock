{-
Tock: a compiler for parallel languages
Copyright (C) 2007  University of Kent

This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation, either version 2 of the License, or (at your
option) any later version.

This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License along
with this program.  If not, see <http://www.gnu.org/licenses/>.
-}

-- | Flatten nested declarations.
module Unnest (unnest) where

import Control.Monad.State
import Data.Generics
import Data.List
import qualified Data.Map as Map
import Data.Maybe

import qualified AST as A
import CompState
import Errors
import EvalConstants
import Metadata
import Pass
import qualified Properties as Prop
import Types

unnest :: [Pass]
unnest = makePassesDep
      [ ("Convert free names to arguments", removeFreeNames, [Prop.mainTagged, Prop.parsWrapped, Prop.functionCallsRemoved], [Prop.freeNamesToArgs])
      , ("Pull nested definitions to top level", removeNesting, [Prop.freeNamesToArgs], [Prop.nestedPulled])
      ]

type NameMap = Map.Map String A.Name

-- | Get the set of free names within a block of code.
freeNamesIn :: Data t => t -> NameMap
freeNamesIn = doGeneric
                `extQ` (ignore :: String -> NameMap)
                `extQ` (ignore :: Meta -> NameMap)
                `extQ` doName `ext1Q` doStructured `extQ` doSpecType
  where
    doGeneric :: Data t => t -> NameMap
    doGeneric n = Map.unions $ gmapQ freeNamesIn n

    ignore :: t -> NameMap
    ignore s = Map.empty

    doName :: A.Name -> NameMap
    doName n | ghostVarPrefix `isPrefixOf` (A.nameName n)
               && ghostVarSuffix `isSuffixOf` (A.nameName n) = Map.empty
             | otherwise =  Map.singleton (A.nameName n) n

    doStructured :: Data a => A.Structured a -> NameMap
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
          A.ForEach _ n b -> (n, freeNamesIn b)

    doSpecType :: A.SpecType -> NameMap
    doSpecType (A.Proc _ _ fs p) = Map.difference (freeNamesIn p) (freeNamesIn fs)
    doSpecType (A.Function _ _ _ fs vp) = Map.difference (freeNamesIn vp) (freeNamesIn fs)
    doSpecType st = doGeneric st

-- | Replace names.
replaceNames :: Data t => [(A.Name, A.Name)] -> t -> t
replaceNames map = doGeneric `extT` doName
  where
    doGeneric :: Data t => t -> t
    doGeneric = (gmapT (replaceNames map))
                                   `extT` (id :: String -> String)
                                   `extT` (id :: Meta -> Meta)  
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
             when (null $ csMainLocals ps) (dieReport (Nothing,"No main process found"))
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
             onds <- mapM (\n -> lookupNameOrError n $ dieP mp $ "Could not find recorded type for free name: " ++ (show $ A.nameName n)) freeNames
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
                            A.Abbrev -> A.ActualVariable (A.Variable m n)
                            _ -> A.ActualExpression (A.ExprVariable m (A.Variable m n))
                          | (am, n) <- zip ams freeNames]
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
removeNesting :: forall a. Data a => A.Structured a -> PassM (A.Structured a)
removeNesting p
    =  do pushPullContext
          p' <- pullSpecs p
          s <- applyPulled p'
          popPullContext
          return s
  where
    pullSpecs :: Data t => t -> PassM t
    pullSpecs = doGeneric `ext1M` doStructured

    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric pullSpecs

    doStructured :: Data t => A.Structured t -> PassM (A.Structured t)
    doStructured s@(A.Spec m spec@(A.Specification _ n st) subS)
        = do isConst <- isConstantName n
             if isConst || canPull st then
                 do debug $ "removeNesting: pulling up " ++ show n
                    spec' <- doGeneric spec
                    addPulled $ (m, Left spec')
                    doStructured subS
               else doGeneric s
    doStructured s = doGeneric s

    canPull :: A.SpecType -> Bool
    canPull (A.Proc _ _ _ _) = True
    canPull (A.RecordType _ _ _) = True
    canPull (A.Protocol _ _) = True
    canPull (A.ProtocolCase _ _) = True
    canPull _ = False

