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

-- | Lists of passes
module PassList (calculatePassList, getPassList) where

import Control.Monad.Error
import Data.Graph.Inductive
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set

import Check
import CompState
import Errors
import GenerateC
import GenerateCPPCSP
import Pass
import qualified Properties as Prop
import RainPasses
import SimplifyComms
import SimplifyExprs
import SimplifyProcs
import SimplifyTypes
import Unnest
import Utils

commonPasses :: CompState -> [Pass]
commonPasses opts = concat $
  [ simplifyTypes
  , makePassesDep' csUsageChecking [("Usage checking", runPassR usageCheckPass, Prop.agg_namesDone, [Prop.parUsageChecked])]
  -- If usage checking is turned off, the pass list will break unless we insert this dummy item:
  , makePassesDep' (not . csUsageChecking) [("Usage checking turned OFF", return, Prop.agg_namesDone, [Prop.parUsageChecked])]
  , simplifyExprs
  , simplifyProcs
  , unnest
  , simplifyComms
  -- The occam frontend does a lot of work for us, so I represent that here:
  ,makePassesDep' ((== FrontendOccam) . csFrontend) [("Null occam pass", return, [],
    Prop.agg_namesDone ++ [Prop.constantsFolded, Prop.expressionTypesChecked, Prop.inferredTypesRecorded, Prop.mainTagged, Prop.processTypesChecked]
  )]
  ]

filterPasses :: CompState -> [Pass] -> [Pass]
filterPasses opts = filter (\p -> passEnabled p opts)

getPassList :: CompState -> [Pass]
getPassList optsPS = filterPasses optsPS $ concat
                                [ rainPasses
                                , commonPasses optsPS
                                , genCPasses
                                , genCPPCSPPasses
                                ]

calculatePassList :: (Die m, CSMR m) => m [Pass]
calculatePassList
  = do st <- getCompState
       let rawList = getPassList st
       case buildGraph (csSanityCheck st) rawList of
         Left err -> dieReport (Nothing, "Error working out pass list: " ++ err)
         Right g -> return $ graphToList (g :: Gr Pass ())

-- Note that the pass execution is "strict" -- that is, all passes
-- are executed, it is only the order that is calculated.  In future,
-- providing we construct the post-conditions carefully, we could
-- have "lazy" passes where we only execute those that have a post-
-- condition that we need later on
graphToList :: Graph gr => gr Pass () -> [Pass]
graphToList = topsort'

buildGraph :: forall gr. Graph gr => Bool -> [Pass] -> Either String (gr Pass ())
buildGraph runProps passes
                  = do checked <- checkedRelations
                       checkPassUnique
                       checkGraph
                       nodes <- labelledNodes
                       edges <- edgeList checked
                       return $ mkGraph nodes edges
  where
    prefixPropName :: String -> String
    prefixPropName = ("_prop_" ++)
  
    allProperties :: [Property] -- find all properties in the passes
    allProperties = nub $ concatMap (\p -> Set.toList (passPre p) ++ Set.toList (passPost p)) passes
  
    propToPass :: Property -> Pass
    propToPass prop = Pass {
      passCode = if runProps then runPassR (\t -> propCheck prop t >> return t) else return
     ,passName = prefixPropName (propName prop)
     ,passPre  = Set.empty
     ,passPost = Set.empty
     ,passEnabled = const True}    
  
    passesAndProps :: [Pass]
    passesAndProps = passes ++ map propToPass allProperties
  
    checkPassUnique :: Either String ()
    checkPassUnique = when (length (nub passesAndProps) /= length passesAndProps) $
                        throwError "Not all pass-names were unique"
  
    -- Maps a property from those with it as a post-condition to those with it as a pre-condition
    relations :: Map.Map Property (Set.Set Pass, Set.Set Pass)
    relations = Map.fromListWith merge $ concatMap toRelation passes
      where
        merge :: (Ord a, Ord b) => (Set.Set a, Set.Set b) -> (Set.Set a, Set.Set b) -> (Set.Set a, Set.Set b)
        merge (xa, xb) (ya, yb) = (Set.union xa ya, Set.union xb yb)
        
        toRelation :: Pass -> [(Property, (Set.Set Pass, Set.Set Pass))]
        toRelation pass = map toPost (Set.toList $ passPost pass) ++ map toPre (Set.toList $ passPre pass)
          where
            toPost :: Property -> (Property, (Set.Set Pass, Set.Set Pass))
            toPost prop = (prop, (Set.singleton pass, Set.empty))
            toPre :: Property -> (Property, (Set.Set Pass, Set.Set Pass))
            toPre prop = (prop, (Set.empty, Set.singleton pass))

    checkedRelations :: Either String (Map.Map Property (Set.Set Pass, Set.Set Pass))
    checkedRelations = liftM Map.fromList $ mapM check $ Map.toList relations
      where
        check :: (Property, (Set.Set Pass, Set.Set Pass)) -> Either String (Property, (Set.Set Pass, Set.Set Pass))
        check (prop, (post, pre))
          = do when (Set.null post && not (Set.null pre)) $
                 throwError $ "Property in dependency graph is required by a pass but not provided by any: "
                   ++ show (map passName $ Set.toList pre)
               return (prop, (post, pre)) --TODO this is an identity transformation, so just check separately
               
    checkGraph :: Either String ()
    checkGraph = return () -- TODO check for cycles

    nodeLabels :: Map.Map Pass Node
    nodeLabels = Map.fromList $ zip passesAndProps [0..]

    lookupPass :: Pass -> Either String Node
    lookupPass p = transformEither ("Internal, should-be-impossible error in lookupPass " ++) id  $ Map.lookup p nodeLabels

    lookupProp :: Property -> Either String Node
    lookupProp p = transformEither ("Internal, should-be-impossible error in lookupProp " ++) id  $ Map.lookup (propToPass p) nodeLabels

    labelledNodes :: Either String [LNode Pass]
    labelledNodes = mapM (\p -> do {lp <- lookupPass p; return (lp, p)}) passesAndProps
    
    edgeList :: Map.Map Property (Set.Set Pass, Set.Set Pass) -> Either String [LEdge ()]
    edgeList = concatMapM (\(prop, (froms, tos)) ->
      do tos' <- mapM lookupPass (Set.toList tos)
         froms' <- mapM lookupPass (Set.toList froms)
         prop' <- lookupProp prop
         return $ [(f, prop', ()) | f <- froms'] ++ [(prop', t, ()) | t <- tos']) . Map.toList
     
