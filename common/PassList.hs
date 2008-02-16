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
module PassList (getPassList) where

import Check
import CompState
import GenerateC
import GenerateCPPCSP
import Pass
import RainPasses
import SimplifyComms
import SimplifyExprs
import SimplifyProcs
import SimplifyTypes
import Unnest

commonPasses :: CompState -> [Pass]
commonPasses opts = concat $
  [ simplifyTypes
  ] ++ (if csUsageChecking opts then [makePasses [("Usage checking", runPassR usageCheckPass)]] else []) ++
  [ simplifyExprs
  , simplifyProcs
  , unnest
  , simplifyComms
  ]


getPassList :: CompState -> [Pass]
getPassList optsPS     = concat [ if csFrontend optsPS == FrontendRain
                                    then rainPasses
                                    else []
                                , commonPasses optsPS
                                , case csBackend optsPS of
                                    BackendC -> genCPasses
                                    BackendCPPCSP -> genCPPCSPPasses
                                    _ -> []
                                ]
