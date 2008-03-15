{-
Tock: a compiler for parallel languages
Copyright (C) 2008  University of Kent

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

-- | The occam-specific frontend passes.
module OccamPasses (occamPasses) where

import Data.Generics

import CompState
import Pass
import qualified Properties as Prop

-- | Occam-specific frontend passes.
occamPasses :: [Pass]
occamPasses = makePassesDep' ((== FrontendOccam) . csFrontend)
    [ ("Dummy occam pass", dummyOccamPass,
       [],
       Prop.agg_namesDone ++ [Prop.constantsFolded, Prop.expressionTypesChecked,
                              Prop.inferredTypesRecorded, Prop.mainTagged,
                              Prop.processTypesChecked])
    ]

-- | A dummy pass for things that haven't been separated out into passes yet.
dummyOccamPass :: Data t => t -> PassM t
dummyOccamPass = return

