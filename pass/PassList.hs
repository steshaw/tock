{-
Tock: a compiler for parallel languages
Copyright (C) 2007, 2008  University of Kent

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

import Control.Monad.State
import Data.List
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import qualified AST as A
import BackendPasses
import Check
import CheckFramework
import CompState
import Errors
import GenerateC
import GenerateCPPCSP
import ImplicitMobility
import Metadata
import OccamPasses
import Pass
import qualified Properties as Prop
import RainPasses
import SimplifyAbbrevs
import SimplifyComms
import SimplifyExprs
import SimplifyProcs
import SimplifyTypes
import Unnest
import Utils

commonPasses :: CompState -> [Pass]
commonPasses opts = concat $
  -- Rain does simplifyTypes separately:
  [ enablePassesWhen ((== FrontendOccam) . csFrontend) simplifyTypes
  , [fixLowReplicators]
  , enablePassesWhen csUsageChecking
    [pass "Usage checking" Prop.agg_namesDone [Prop.parUsageChecked]
      (passOnlyOnAST "usageCheckPass" usageCheckPass)]
  -- If usage checking is turned off, the pass list will break unless we insert this dummy item:
  , enablePassesWhen (not . csUsageChecking)
    [pass "Usage checking turned OFF" Prop.agg_namesDone [Prop.parUsageChecked]
      return]
    -- TODO add an implicit mobility pass after these two:
  , enablePassesWhen csClassicOccamMobility [mobiliseArrays, inferDeref]
  , simplifyAbbrevs
  , simplifyComms
  , simplifyExprs
  , simplifyProcs
  , unnest
  , enablePassesWhen csUsageChecking
     [abbrevCheckPass]
  , squashArrays
  , [pass "Removing unused variables" [] []
      (passOnlyOnAST "checkUnusedVar" (runChecks checkUnusedVar))]
  ]

filterPasses :: CompState -> [Pass] -> [Pass]
filterPasses opts = filter (\p -> passEnabled p opts)

-- This pass is so small that we may as well just give it here:
nullStateBodies :: Pass
nullStateBodies = Pass
  {passCode = \t ->
    ((get >>* \st -> st {csNames = Map.map nullProcFuncDefs (csNames st)}) >>= put)
    >> return t
  ,passName = "Remove process and function bodies from compiler state"
  ,passPre = Set.empty
  ,passPost = Set.empty
  ,passEnabled = const True}
  where
    nullProcFuncDefs :: A.NameDef -> A.NameDef
    nullProcFuncDefs (A.NameDef m n on (A.Proc m' sm fs _) am ns pl)
      = (A.NameDef m n on (A.Proc m' sm fs (A.Skip m')) am ns pl)
    nullProcFuncDefs (A.NameDef m n on (A.Function m' sm ts fs (Left _)) am ns pl)
      = (A.NameDef m n on (A.Function m' sm ts fs (Left $ A.Several m' [])) am ns pl)
    nullProcFuncDefs (A.NameDef m n on (A.Function m' sm ts fs (Right _)) am ns pl)
      = (A.NameDef m n on (A.Function m' sm ts fs (Right $ A.Skip m')) am ns pl)
    nullProcFuncDefs x = x
    

getPassList :: CompState -> [Pass]
getPassList optsPS = checkList $ filterPasses optsPS $ concat
                                [ [nullStateBodies]
                                , occamPasses
                                , rainPasses
                                , commonPasses optsPS
                                , genCPasses
                                , genCPPCSPPasses
                                ]

calculatePassList :: CSMR m => m [Pass]
calculatePassList
    =  do optsPS <- getCompState
          let passes = getPassList optsPS
          return $ if csSanityCheck optsPS
                     then addChecks passes
                     else passes
  where
    -- | Add extra passes to check that properties hold.
    -- Each property will be checked after the last pass that provides it has
    -- run.
    addChecks :: [Pass] -> [Pass]
    addChecks = reverse . (addChecks' Set.empty) . reverse

    addChecks' :: Set Property -> [Pass] -> [Pass]
    addChecks' _ [] = []
    addChecks' checked (p:ps) = checks ++ [p] ++ addChecks' checked' ps
      where
        props = Set.difference (passPost p) checked
        checked' = Set.union checked props

        checks = [pass ("[" ++ propName prop ++ "]")
                       []
                       []
                       (passOnlyOnAST "prop" $ checkProp prop)
                  | prop <- Set.toList props]

        checkProp :: Property -> A.AST -> PassM A.AST
        checkProp prop ast = propCheck prop ast >> return ast

-- | If something isn't right, it gives back a list containing a single pass
-- that will give an error.
checkList :: [Pass] -> [Pass]
checkList passes
    = case check [] passes of
        Left err -> [pass "Pass list internal error"
                          []
                          []
                          (const $ dieP emptyMeta err)
                    ]
        Right ps -> ps
  where
    check :: [Pass] -> [Pass] -> Either String [Pass]
    check prev [] = Right prev
    check prev (p:ps)
      = case filter givesPrereq (p:ps) of
          -- Check that our pre-requisites are not supplied by a later pass
          -- or supplied by the pass that needs them:
          (x:_) ->
             Left $ "Pass order not correct; one of the pre-requisites"
               ++ " for pass: " ++ (passName p) ++ " is supplied in a later"
               ++ " pass: " ++ (passName x) ++ ", pre-requisites in question"
               ++ " are: " ++ show (Set.intersection (passPost x) (passPre p))
                -- Now check that someone supplied our pre-requisites:
          [] -> if Set.null (passPre p) || any givesPrereq prev
                  then check (prev ++ [p]) ps
                  else Left $ "Pass order not correct; one of the pre-requisites"
                   ++ " for pass: " ++ (passName p) ++ "is not supplied"
                   ++ " by a prior pass, pre-requisites are: "
                   ++ show (passPre p)
      where
        givesPrereq :: Pass -> Bool
        givesPrereq p' = not $ Set.null $
          Set.intersection (passPost p') (passPre p)
