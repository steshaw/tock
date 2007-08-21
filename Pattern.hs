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
  deriving (Typeable,Show,Eq)

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
