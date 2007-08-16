module TreeUtil (Pattern(..), MatchErrors, AnyDataItem(..), Items, assertPatternMatch, getMatchedItems, mkPattern, tag0, tag1, tag2, tag3, tag4, tag5, tag6, tag7) where

import Test.HUnit hiding (State)
import qualified Data.Map as Map
import Control.Monad.State
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
  
type MatchErrors = [String]

-- | A function for asserting equality over generic types.  Like assertEqual, but it can take items of different types to compare
--   The "Plain" suffix arises from the fact that the types should not contain (at the top-level or nested)
--   any "Pattern" items.
assertGenEqualPlain :: (Data a, Data b) => String -> a -> b -> MatchErrors
assertGenEqualPlain s x y = do case (checkEqual x y) of
                                 True -> []
                                 False -> [s ++ "; Items not equal, expected: " ++ (gshow x) ++ " but got: " ++ (gshow y)]
  where
    checkEqual x y = case (cast y) of
      -- | Same type, use the library-provided geq function to compare them
      Just y' -> geq x y'
      -- | Different types, so not equal
      Nothing -> False

-- | A data item used when matching items of interest.  Note that it is similar to Pattern but not the same;
--   AnyDataItem can only contain Data, and has no other special values.
data AnyDataItem = forall a. Data a => ADI a

-- | A type representing the state involved in recording items of interest.  It is simply a map
--   from arbitrary string keys to AnyDataItem, which is just a wrapper for any item of class Data
type Items = Map.Map String AnyDataItem

-- | A function that takes a string key (of an item of interest), and a value.
--   If the key has NOT been seen before, checkItem merely records its value in the set of items of interest
--   If the key has been seen before, checkItem checks that the new (passed) value matches the old value.
checkItem :: Data z => String -> z -> State Items MatchErrors
checkItem key val 
  = do items <- get
       case Map.lookup key items of
         Just (ADI val') -> return (assertGenEqualPlain "Item of interest does not match prior value" val' val)
         Nothing -> do {put (Map.insert key (ADI val) items) ; return [] }

-- | A function that takes an expected Pattern value, an actual Data value, and returns the appropriate checks
--   for pseudo-equality.  This pseudo-equality is equality, enhanced by the possibility of Pattern's 
--   DontCare and Named (item-of-interest) values which match differently.
checkMatch :: Data z => Pattern -> z -> State Items MatchErrors
-- | DontCare matches anything, so return an empty assertion:
checkMatch DontCare _ = return []
-- | Items of interest are delegated to the checkItem function that uses the Items state
checkMatch (Named s p) b = sequenceS [checkMatch p b, checkItem s b]
-- | Constructors are matched using the applyAll function (but we must also check the constructors are equal)
checkMatch (Match con items) b 
  = do conEq <- checkEq con (toConstr b)
       case conEq of
         [] -> sequenceS $ (applyAll items b)
         _ -> return conEq --no point comparing fields if the constructors don't match
  where 
    checkEq :: Constr -> Constr -> State Items MatchErrors 
    checkEq a b = if (a == b) 
                  then return []
                  else return ["Constructors not equal, expected: " ++ (show a) ++ " actual: " ++ (show b)]
 
    -- | applyAll checks that the non-constructor items of an algebraic data type are matched:
    applyAll :: Data z => [Pattern] -> z -> [State Items MatchErrors]
    applyAll list d = map (applyAll' d) (zip [0..] list)
    applyAll' :: Data z => z -> (Int,Pattern) -> State Items MatchErrors
    applyAll' d (index,f) 
      = if (index >= numIndexes) 
        then return ["Invalid index in applyAll: " ++ (show index) ++ ", numIndexes is: " ++ (show numIndexes) 
               ++ " trying to check, expected: " ++ (show f) ++ " actual: " ++ (gshow d)]
        else (gmapQi index (checkMatch f) d) 
      --Possibly a better way?
      where
        numIndexes = length (gmapQ (const 0) d)


-- | A helper function for concating awkward lists in monads
sequenceS :: [State Items MatchErrors] -> State Items MatchErrors
--We have [State Items MatchErrors]
--We want State Items MatchErrors
--sequence :: [State Items MatchErrors] -> State Items [MatchErrors]
--concat :: [MatchErrors] -> MatchErrors
sequenceS x = (liftM concat) (sequence x)    

-- | A function for checking that two Data items (expected, actual) match, where the expected item (LHS)
--   may contain special Pattern values (such as DontCare, Named, etc)
assertPatternMatch :: (Data y, Data z) => String -> y -> z -> Assertion
assertPatternMatch msg exp act = 
-- Uncomment this line for debugging help:
--         putStrLn ("Testing: " ++ (gshow a) ++ " vs " ++ (gshow b)) >> 
         sequence_ $ map (assertFailure . ((++) msg)) (evalState (checkMatch (mkPattern exp) act) (Map.empty))

-- | A function for getting the matched items from the patterns on the LHS
--   Either returns the matched items, or a list of errors from the matching
getMatchedItems :: (Data y, Data z) => y -> z -> Either Items MatchErrors
getMatchedItems a b 
  = case errors of
      [] -> Left items
      _ -> Right errors
    where (errors,items) = runState (checkMatch (mkPattern a) b) (Map.empty)


--The mkPattern function needs to be able to take things such as:
-- v :: Pattern
-- (w:ws) :: [Pattern]
-- (x0,x1) :: (Pattern,Pattern)
-- (y0,y1,y2) :: Data b => (Pattern,Pattern,b)
--And return an Pattern:
-- v
-- Match (:) [w,mkPattern ws]
-- Match (,) [x0,x1]
-- Match (,,) [y0,y1,mkPattern u]
--The latter three could be rephrased as:
-- Match (:) [mkPattern w,mkPattern ws]
-- Match (,) [mkPattern x0,mkPattern x1]
-- Match (,,) [mkPattern y0,mkPattern y1,mkPattern u]
--Therefore the whole function can be viewed as: get the constructor, and map mkPattern over the sub-elements

mkPattern :: (Data a) => a -> Pattern
mkPattern x = case ((cast x) :: Maybe Pattern) of
  Just x' -> x'
  Nothing -> Match (toConstr x) (gmapQ mkPattern x)

--I'm not sure tag0 is ever needed, but just in case:
tag0 :: (Data a) => a -> Pattern
tag0 con = (Match (toConstr con) [])


-- | A helper function.  The parameters are: constructor item0 item1, where the constructor has arity 2
tag1 :: (Data a, Data b0) => (a0  -> a) -> b0 -> Pattern
tag1 con x0 = (Match (toConstr con') [mkPattern x0])
  where
    con' = con (undefined :: a0)

-- | A helper function.  The parameters are: constructor item0 item1, where the constructor has arity 2
tag2 :: (Data a, Data b0, Data b1) => (a0 -> a1 -> a) -> b0 -> b1 -> Pattern
tag2 con x0 x1 = (Match (toConstr con') [mkPattern x0,mkPattern x1])
  where
    con' = con (undefined :: a0) (undefined :: a1)

-- | A helper function.  The parameters are: constructor item0 item1 item2, where the constructor has arity 3
tag3 :: (Data a, Data b0, Data b1, Data b2) => (a0 -> a1 -> a2 -> a) -> b0 -> b1 -> b2 -> Pattern
tag3 con x0 x1 x2 = (Match (toConstr con') [mkPattern x0,mkPattern x1,mkPattern x2])
  where
    con' = con (undefined :: a0) (undefined :: a1) (undefined :: a2)

-- | A helper function.  The parameters are: constructor item0 item1 item2 item3, where the constructor has arity 4
tag4 :: (Data a, Data b0, Data b1, Data b2, Data b3) => (a0 -> a1 -> a2 -> a3 -> a) -> b0 -> b1 -> b2 -> b3 -> Pattern
tag4 con x0 x1 x2 x3 = (Match (toConstr con') [mkPattern x0,mkPattern x1,mkPattern x2,mkPattern x3])
  where
    con' = con (undefined :: a0) (undefined :: a1) (undefined :: a2) (undefined :: a3)

-- | A helper function.  The parameters are: constructor item0 item1 item2 item3 item4, where the constructor has arity 5
tag5 :: (Data a, Data b0, Data b1, Data b2, Data b3, Data b4) => 
          (a0 -> a1 -> a2 -> a3 -> a4 -> a) -> b0 -> b1 -> b2 -> b3 -> b4 -> Pattern
tag5 con x0 x1 x2 x3 x4 = (Match (toConstr con') [mkPattern x0,mkPattern x1,mkPattern x2,mkPattern x3,mkPattern x4])
  where
    con' = con (undefined :: a0) (undefined :: a1) (undefined :: a2) (undefined :: a3) (undefined :: a4)
    
-- | A helper function.  The parameters are: constructor item0 item1 item2 item3 item4 item5, where the constructor has arity 6
tag6 :: (Data a, Data b0, Data b1, Data b2, Data b3, Data b4, Data b5) => 
          (a0 -> a1 -> a2 -> a3 -> a4 -> a5 -> a) -> b0 -> b1 -> b2 -> b3 -> b4 -> b5 -> Pattern
tag6 con x0 x1 x2 x3 x4 x5 = (Match (toConstr con') [mkPattern x0,mkPattern x1,mkPattern x2,mkPattern x3,mkPattern x4,mkPattern x5])
  where
    con' = con (undefined :: a0) (undefined :: a1) (undefined :: a2) (undefined :: a3) (undefined :: a4) (undefined :: a5)


-- | A helper function.  The parameters are: constructor item0 item1 item2 item3 item4 item5 item6, where the constructor has arity 7
tag7 :: (Data a, Data b0, Data b1, Data b2, Data b3, Data b4, Data b5, Data b6) => 
          (a0 -> a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a) -> b0 -> b1 -> b2 -> b3 -> b4 -> b5 -> b6 -> Pattern
tag7 con x0 x1 x2 x3 x4 x5 x6 = (Match (toConstr con') [mkPattern x0,mkPattern x1,mkPattern x2,mkPattern x3,mkPattern x4,mkPattern x5,mkPattern x6])
  where
    con' = con (undefined :: a0) (undefined :: a1) (undefined :: a2) (undefined :: a3) (undefined :: a4) (undefined :: a5) (undefined :: a6)
