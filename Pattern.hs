module Pattern (Pattern(..)) where

import Data.Generics

data Pattern =
    -- | We don't care what the value is -- will match against any item
    DontCare
    -- | A named "item of interest".  Given the specified key, all data items with the same key should be identical (otherwise match errors will be given)
    | Named String Pattern
    -- | A constructed item.  This is special because the sub-items may not be of the right type for the constructor,
    --   because they may be special items (such as DontCare)
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
  
ty_Pattern = mkDataType "TreeUtil.Pattern"
   [
    constr_DontCare
    ,constr_Named
    ,constr_Match
   ]
 
constr_DontCare = mkConstr ty_Pattern "DontCare" [] Prefix
constr_Named = mkConstr ty_Pattern "Named" [] Prefix
constr_Match = mkConstr ty_Pattern "Match" [] Prefix
