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
import Data.List
import qualified Data.Set as Set

import BackendPasses
import Check
import CompState
import Errors
import GenerateC
import GenerateCPPCSP
import Metadata
import OccamPasses
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
  -- Rain does simplifyTypes separately:
  [ enablePassesWhen ((== FrontendOccam) . csFrontend) simplifyTypes
  , makePassesDep' csUsageChecking [("Usage checking", runPassR usageCheckPass, Prop.agg_namesDone, [Prop.parUsageChecked])]
  -- If usage checking is turned off, the pass list will break unless we insert this dummy item:
  , makePassesDep' (not . csUsageChecking) [("Usage checking turned OFF", return, Prop.agg_namesDone, [Prop.parUsageChecked])]
  , simplifyComms
  , simplifyExprs
  , simplifyProcs
  , unnest
  , squashArrays
  ]

filterPasses :: CompState -> [Pass] -> [Pass]
filterPasses opts = filter (\p -> passEnabled p opts)

getPassList :: CompState -> [Pass]
getPassList optsPS = checkList $ filterPasses optsPS $ concat
                                [ occamPasses
                                , rainPasses
                                , commonPasses optsPS
                                , genCPasses
                                , genCPPCSPPasses
                                ]

calculatePassList :: CSMR m => m [Pass]
calculatePassList = getCompState >>* getPassList

--TODO put back the sanity check option to enable the property checking

-- | If something isn't right, it gives back a list containing a single pass
-- that will give an error.
checkList :: [Pass] -> [Pass]
checkList passes = case check [] passes of
    Left err -> [Pass {passCode = const $ dieP emptyMeta err
                      ,passName = "Pass List Error"
                      ,passPre = Set.empty
                      ,passPost = Set.empty
                      ,passEnabled = const True}
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
