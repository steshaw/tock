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

-- | Simplify abbreviations.
module SimplifyAbbrevs (simplifyAbbrevs) where

import qualified AST as A
import Pass
import qualified Properties as Prop
import Traversal

simplifyAbbrevs :: [Pass]
simplifyAbbrevs =
    [ removeInitial
    , removeResult
    ]

-- | Rewrite 'InitialAbbrev' into a variable and an assignment.
removeInitial :: Pass
removeInitial
    = pass "Remove INITIAL abbreviations"
           []
           [Prop.initialRemoved]
           -- FIXME: Implement this
           return

-- | Rewrite 'ResultAbbrev' into just 'Abbrev'.
removeResult :: Pass
removeResult
    = pass "Remove RESULT abbreviations"
           []
           [Prop.resultRemoved]
           (applyDepthM (return . doAbbrevMode))
  where
    doAbbrevMode :: A.AbbrevMode -> A.AbbrevMode
    doAbbrevMode A.ResultAbbrev = A.Abbrev
    doAbbrevMode s = s

