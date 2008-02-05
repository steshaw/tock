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

-- | The module containing the definition of the Pattern data-type.  For details on using 'Pattern', see the "TreeUtil" module.
module Pattern (Pattern(..)) where

import Data.Generics

-- | A Pattern that can match any Haskell data structure.  Its implementation of 'Data' is incomplete ('gunfold' will give an error).
data Pattern =
    -- | We don't care what the value is -- will match against any item.
    DontCare
    -- | A named item of interest with the given 'String' key.  For any key, all data items with the same key should be identical (otherwise match errors will be given)
    | Named String Pattern
    -- | A constructed item.
    | Match Constr [Pattern]
  deriving (Typeable,Show)
  
--Tests if patterns are identical, NOT if they'll match the same thing:
instance Eq Pattern where
  (==) DontCare DontCare = True
  (==) (Named s0 p0) (Named s1 p1) = (s0 == s1) && (p0 == p1)
  (==) (Match c0 ps0) (Match c1 ps1) = (c0 == c1) && (show c0 == show c1) && (ps0 == ps1)
  (==) _ _ = False

--No proper gunfold, as I still can't figure out to implement it (Constr is problematic)
instance Data Pattern where
  toConstr (DontCare) = constr_DontCare
  toConstr (Named {}) = constr_Named
  toConstr (Match {}) = constr_Match

  gunfold _ _ _ = error "gunfold Pattern"
  
  dataTypeOf _ = ty_Pattern

ty_Pattern :: DataType  
ty_Pattern = mkDataType "TreeUtil.Pattern"
   [
    constr_DontCare
    ,constr_Named
    ,constr_Match
   ]

constr_DontCare, constr_Named, constr_Match :: Constr
 
constr_DontCare = mkConstr ty_Pattern "DontCare" [] Prefix
constr_Named = mkConstr ty_Pattern "Named" [] Prefix
constr_Match = mkConstr ty_Pattern "Match" [] Prefix
