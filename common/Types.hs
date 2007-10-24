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

-- | Type inference and checking.
module Types
  (
    specTypeOfName, typeOfSpec, abbrevModeOfName, typeOfName, typeOfExpression, typeOfVariable, underlyingType, stripArrayType, abbrevModeOfVariable, abbrevModeOfSpec
    , isRealType, isIntegerType, isCaseableType, resolveUserType, isSafeConversion, isPreciseConversion, isImplicitConversionRain
    , returnTypesOfFunction
    , BytesInResult(..), bytesInType, sizeOfReplicator, sizeOfStructured

    , makeAbbrevAM, makeConstant, addOne
    , addDimensions, removeFixedDimensions, trivialSubscriptType, subscriptType, unsubscriptType
    , recordFields, protocolItems

	, leastGeneralSharedTypeRain

  ) where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe
import Data.List
import Data.Ord

import qualified AST as A
import CompState
import Errors
import EvalLiterals
import Intrinsics
import Metadata
import ShowCode
import Utils

-- | Gets the 'A.SpecType' for a given 'A.Name' from the recorded types in the 'CompState'.  Dies with an error if the name is unknown.
specTypeOfName :: (CSM m, Die m) => A.Name -> m A.SpecType
specTypeOfName n
    = liftM A.ndType (lookupNameOrError n $ dieP (A.nameMeta n) $ "Could not find find type in specTypeOfName for: " ++ (show $ A.nameName n))

-- | Gets the 'A.AbbrevMode' for a given 'A.Name' from the recorded types in the 'CompState'.  Dies with an error if the name is unknown.
abbrevModeOfName :: (CSM m, Die m) => A.Name -> m A.AbbrevMode
abbrevModeOfName n
    = liftM A.ndAbbrevMode (lookupNameOrError n $ dieP (A.nameMeta n) $ "Could not find find abbreviation mode in abbrevModeOfName for: " ++ (show $ A.nameName n))

-- | Gets the 'A.Type' for a given 'A.Name' by looking at its definition in the 'CompState'.  Dies with an error if the name is unknown.
typeOfName :: (CSM m, Die m) => A.Name -> m A.Type
typeOfName n
    =  do st <- specTypeOfName n
          t <- typeOfSpec st
          case t of
            Just t' -> return t'
            Nothing -> die $ "cannot type name " ++ show st

typeOfSpec :: (CSM m, Die m) => A.SpecType -> m (Maybe A.Type)
typeOfSpec st
        = case st of
            A.Declaration _ t -> return $ Just t
            A.Is _ _ _ v -> (liftM Just) (typeOfVariable v)
            A.IsExpr _ _ _ e -> (liftM Just) (typeOfExpression e)
            A.IsChannelArray _ _ (c:_) -> liftM (Just . (A.Array [A.UnknownDimension])) $ typeOfVariable c
            A.Retypes _ _ t _ -> return $ Just t
            A.RetypesExpr _ _ t _ -> return $ Just t
            _ -> return Nothing

--{{{  identifying types
-- | Apply a slice to a type.
sliceType :: (CSM m, Die m) => Meta -> A.Expression -> A.Expression -> A.Type -> m A.Type
sliceType m base count (A.Array (d:ds) t)
    = case (isConstant base, isConstant count) of
        (True, True) ->
          do b <- evalIntExpression base
             c <- evalIntExpression count
             case d of
               A.Dimension size ->
                 if (size - b) < c
                   then dieP m $ "invalid slice " ++ show b ++ " -> " ++ show c ++ " of " ++ show size
                   else return $ A.Array (A.Dimension c : ds) t
               A.UnknownDimension ->
                 return $ A.Array (A.Dimension c : ds) t
        (True, False) -> return $ A.Array (A.UnknownDimension : ds) t
        (False, True) ->
          do c <- evalIntExpression count
             return $ A.Array (A.Dimension c : ds) t
        (False, False) -> return $ A.Array (A.UnknownDimension : ds) t
sliceType m _ _ _ = dieP m "slice of non-array type"

-- | Get the fields of a record type.
recordFields :: (CSM m, Die m) => Meta -> A.Type -> m [(A.Name, A.Type)]
recordFields m (A.Record rec)
    =  do st <- specTypeOfName rec
          case st of
            A.RecordType _ _ fs -> return fs
            _ -> dieP m "not record type"
recordFields m _ = dieP m "not record type"

-- | Get the type of a record field.
typeOfRecordField :: (CSM m, Die m) => Meta -> A.Type -> A.Name -> m A.Type
typeOfRecordField m t field
    =  do fs <- recordFields m t
          checkJust "unknown record field" $ lookup field fs

-- | Apply a plain subscript to a type.
plainSubscriptType :: (CSM m, Die m) => Meta -> A.Expression -> A.Type -> m A.Type
plainSubscriptType m sub (A.Array (d:ds) t)
    = case (isConstant sub, d) of
        (True, A.Dimension size) ->
          do i <- evalIntExpression sub
             if (i < 0) || (i >= size)
               then dieP m $ "invalid subscript " ++ show i ++ " of " ++ show size
               else return ok
        _ -> return ok
  where
    ok = case ds of
           [] -> t
           _ -> A.Array ds t
plainSubscriptType m _ t = diePC m $ formatCode "subscript of non-array type: %" t

-- | Apply a subscript to a type, and return what the type is after it's been
-- subscripted.
subscriptType :: (CSM m, Die m) => A.Subscript -> A.Type -> m A.Type
subscriptType sub t@(A.UserDataType _)
    = resolveUserType t >>= subscriptType sub
subscriptType (A.SubscriptFromFor m base count) t
    = sliceType m base count t
subscriptType (A.SubscriptFrom m base) (A.Array (d:ds) t)
    = case (isConstant base, d) of
        (True, A.Dimension size) ->
          do b <- evalIntExpression base
             if (size - b) < 0
               then dieP m $ "invalid slice " ++ show b ++ " -> end of " ++ show size
               else return $ A.Array (A.Dimension (size - b) : ds) t
        _ -> return $ A.Array (A.UnknownDimension : ds) t
subscriptType (A.SubscriptFor m count) t
    = sliceType m (makeConstant emptyMeta 0) count t
subscriptType (A.SubscriptField m tag) t = typeOfRecordField m t tag
subscriptType (A.Subscript m sub) t = plainSubscriptType m sub t
subscriptType sub t = diePC (findMeta sub) $ formatCode "Unsubscriptable type: %" t

-- | The inverse of 'subscriptType': given a type that we know is the result of
-- a subscript, return what the type being subscripted is.
unsubscriptType :: (CSM m, Die m) => A.Subscript -> A.Type -> m A.Type
unsubscriptType (A.SubscriptFromFor _ _ _) t
    = return $ removeFixedDimension t
unsubscriptType (A.SubscriptFrom _ _) t
    = return $ removeFixedDimension t
unsubscriptType (A.SubscriptFor _ _) t
    = return $ removeFixedDimension t
unsubscriptType (A.SubscriptField _ _) t
    = die $ "unsubscript of record type (but we can't tell which one)"
unsubscriptType (A.Subscript _ sub) t
    = return $ addDimensions [A.UnknownDimension] t

-- | Just remove the first dimension from an array type -- like doing
-- subscriptType with constant 0 as a subscript, but without the checking.
-- This is used for the couple of cases where we know it's safe and don't want
-- the usage check.
trivialSubscriptType :: (CSM m, Die m) => A.Type -> m A.Type
trivialSubscriptType (A.Array [d] t) = return t
trivialSubscriptType (A.Array (d:ds) t) = return $ A.Array ds t
trivialSubscriptType t = dieC $ formatCode "not plain array type: %" t

-- | Gets the 'A.Type' of a 'A.Variable' by looking at the types recorded in the 'CompState'.
typeOfVariable :: (CSM m, Die m) => A.Variable -> m A.Type
typeOfVariable (A.Variable m n) = typeOfName n
typeOfVariable (A.SubscriptedVariable m s v)
    = typeOfVariable v >>= subscriptType s
typeOfVariable (A.DerefVariable m v)
    = do t <- typeOfVariable v
         case t of
           (A.Mobile innerT) -> return innerT
           _ -> die $ "Tried to dereference a non-mobile variable: " ++ show v
typeOfVariable (A.DirectedVariable m dir v)
    = do t <- typeOfVariable v
         case t of 
           (A.Chan A.DirUnknown attr innerT) -> return (A.Chan dir attr innerT)
           _ -> die $ "Used specifier on something that was not a directionless channel: " ++ show v

-- | Get the abbreviation mode of a variable.
abbrevModeOfVariable :: (CSM m, Die m) => A.Variable -> m A.AbbrevMode
abbrevModeOfVariable (A.Variable _ n) = abbrevModeOfName n
abbrevModeOfVariable (A.SubscriptedVariable _ sub v) = abbrevModeOfVariable v
abbrevModeOfVariable (A.DirectedVariable _ _ v) = abbrevModeOfVariable v
abbrevModeOfVariable (A.DerefVariable _ v) = return A.Original

dyadicIsBoolean :: A.DyadicOp -> Bool
dyadicIsBoolean A.Eq = True
dyadicIsBoolean A.NotEq = True
dyadicIsBoolean A.Less = True
dyadicIsBoolean A.More = True
dyadicIsBoolean A.LessEq = True
dyadicIsBoolean A.MoreEq = True
dyadicIsBoolean A.After = True
dyadicIsBoolean _ = False

-- | Gets the 'A.Type' of an 'A.Expression'.  This function assumes that the expression has already been type-checked.
typeOfExpression :: (CSM m, Die m) => A.Expression -> m A.Type
typeOfExpression e
    = case e of
        A.Monadic m op e -> typeOfExpression e
        A.Dyadic m op e f ->
          if dyadicIsBoolean op then return A.Bool 
          else
            --Need to handle multiplying Time types specially, due to the asymmetry:           
            if (op == A.Times)
              then do tlhs <- typeOfExpression e
                      trhs <- typeOfExpression f
                      if (tlhs == A.Time || trhs == A.Time)
                        then return A.Time
                        else return tlhs
              else typeOfExpression e
        A.MostPos m t -> return t
        A.MostNeg m t -> return t
        A.SizeType m t -> return A.Int
        A.SizeExpr m t -> return A.Int
        A.SizeVariable m t -> return A.Int
        A.Conversion m cm t e -> return t
        A.ExprVariable m v -> typeOfVariable v
        A.Literal _ t _ -> return t
        A.True m -> return A.Bool
        A.False m -> return A.Bool
        A.FunctionCall m n es -> liftM head $ returnTypesOfFunction n
        A.IntrinsicFunctionCall _ s _ -> liftM head $ returnTypesOfIntrinsic s
        A.SubscriptedExpr m s e ->
          typeOfExpression e >>= subscriptType s
        A.BytesInExpr m e -> return A.Int
        A.BytesInType m t -> return A.Int
        A.OffsetOf m t n -> return A.Int
        A.ExprConstr m (A.RangeConstr _ b e) -> 
          do bt <- typeOfExpression b
             et <- typeOfExpression e
             if bt == et then return (A.Array [A.UnknownDimension] bt) else dieP m "Types did not match for beginning and end of range"
        A.ExprConstr m (A.RepConstr _ rep e) -> 
          do t <- typeOfExpression e 
             count <- evalIntExpression $ sizeOfReplicator rep
             return $ A.Array [A.Dimension count] t
        A.AllocMobile _ t _ -> return t
--}}}

-- | Gets the return type(s) of a function call from the 'CompState'.
returnTypesOfFunction :: (CSM m, Die m) => A.Name -> m [A.Type]
returnTypesOfFunction n
    =  do st <- specTypeOfName n
          case st of
            A.Function _ _ rs _ _ -> return rs
            -- If it's not defined as a function, it might have been converted to a proc.
            _ ->
              do ps <- get
                 checkJust "not defined as a function" $
                   Map.lookup (A.nameName n) (csFunctionReturns ps)

returnTypesOfIntrinsic :: (CSM m, Die m) => String -> m [A.Type]
returnTypesOfIntrinsic s
    = case lookup s intrinsicFunctions of
        Just (rts, _) -> return rts
        Nothing -> die $ "unknown intrinsic function " ++ s

-- | Get the items in a channel's protocol (for typechecking).
-- Returns Left if it's a simple protocol, Right if it's tagged.
protocolItems :: (CSM m, Die m) => A.Variable -> m (Either [A.Type] [(A.Name, [A.Type])])
protocolItems v
    =  do A.Chan _ _ t <- typeOfVariable v
          case t of
            A.UserProtocol proto ->
              do st <- specTypeOfName proto
                 case st of
                   A.Protocol _ ts -> return $ Left ts
                   A.ProtocolCase _ nts -> return $ Right nts
            _ -> return $ Left [t]

-- | Gets the 'A.AbrrevMode' of a 'A.SpecType' directly.
abbrevModeOfSpec :: A.SpecType -> A.AbbrevMode
abbrevModeOfSpec s
    = case s of
        A.Is _ am _ _ -> am
        A.IsExpr _ am _ _ -> am
        A.IsChannelArray _ _ _ -> A.Abbrev
        A.Retypes _ am _ _ -> am
        A.RetypesExpr _ am _ _ -> am
        _ -> A.Original

-- | Resolve a datatype into its underlying type -- i.e. if it's a named data
-- type, then return the underlying real type. This will recurse.
underlyingType :: (CSM m, Die m) => A.Type -> m A.Type
underlyingType = everywhereM (mkM underlyingType')
  where
    underlyingType' :: (CSM m, Die m) => A.Type -> m A.Type
    underlyingType' t@(A.UserDataType _)
      = resolveUserType t >>= underlyingType
    underlyingType' (A.Array ds t) = return $ addDimensions ds t
    underlyingType' t = return t

-- | Like underlyingType, but only do the "outer layer": if you give this a
-- user type that's an array of user types, then you'll get back an array of
-- user types.
resolveUserType :: (CSM m, Die m) => A.Type -> m A.Type
resolveUserType (A.UserDataType n)
    =  do st <- specTypeOfName n
          case st of
            A.DataType _ t -> resolveUserType t
            _ -> die $ "not a type name " ++ show n
resolveUserType t = return t

-- | Add array dimensions to a type; if it's already an array it'll just add
-- the new dimensions to the existing array.
addDimensions :: [A.Dimension] -> A.Type -> A.Type
addDimensions newDs (A.Array ds t) = A.Array (newDs ++ ds) t
addDimensions ds t = A.Array ds t

-- | Return a type with any enclosing arrays removed; useful for identifying
-- things that should be channel names, timer names, etc. in the parser.
stripArrayType :: A.Type -> A.Type
stripArrayType (A.Array _ t) = stripArrayType t
stripArrayType t = t

-- | Remove one fixed dimension from a type.
removeFixedDimension :: A.Type -> A.Type
removeFixedDimension (A.Array (A.Dimension _:ds) t) = A.Array (A.UnknownDimension:ds) t
removeFixedDimension t = t

-- | Remove any fixed array dimensions from a type.
removeFixedDimensions :: A.Type -> A.Type
removeFixedDimensions (A.Array ds t) = A.Array [A.UnknownDimension | _ <- ds] t
removeFixedDimensions t = t

-- | Given the abbreviation mode of something, return what the abbreviation
-- mode of something that abbreviated it would be.
makeAbbrevAM :: A.AbbrevMode -> A.AbbrevMode
makeAbbrevAM A.Original = A.Abbrev
makeAbbrevAM am = am

-- | Generate a constant expression from an integer -- for array sizes and the like.
makeConstant :: Meta -> Int -> A.Expression
makeConstant m n = A.Literal m A.Int $ A.IntLiteral m (show n)

-- | Checks whether a given conversion can be done implicitly in Rain
-- Parameters are src dest
isImplicitConversionRain :: A.Type -> A.Type -> Bool
isImplicitConversionRain x y
  = if (x == y)
      then True
      else if (x == A.Bool || y == A.Bool)
             then False
             else isSafeConversion x y

-- | Is a conversion between two types precise (i.e. do you need to specify
-- ROUND or TRUNC when doing it)?
isPreciseConversion :: A.Type -> A.Type -> Bool
isPreciseConversion A.Real32 A.Real64 = True
isPreciseConversion fromT toT
    = fromT == toT || not (isRealType fromT || isRealType toT)

-- | Will a conversion between two types always succeed?
--Parameters are src dest
isSafeConversion :: A.Type -> A.Type -> Bool
isSafeConversion A.Real32 A.Real64 = True
isSafeConversion src dest = (src' == dest') || ((src' == A.Bool || isIntegerType src') && (dest' == A.Bool || isIntegerType dest') && (findCastRoute dest' src'))
  where
    src' = convInt src
    dest' = convInt dest

    --Turn Int into Int32:
    convInt :: A.Type -> A.Type
    convInt A.Int = A.Int32
    convInt t = t

    --Parameters are dest src
    findCastRoute :: A.Type -> A.Type -> Bool
    findCastRoute dest src
        --Either a direct converstion is possible
      = (elem (dest,src) possibleConversions)
        --Or there exists some chained conversion:
        || (any (findCastRoute dest) (findDests src possibleConversions))

    --Finds all the conversions from the src type using the given list of (dest,src)
    --Note that the list must not allow any cycles!  (or else we will engage in infinite recursion)
    findDests :: A.Type -> [(A.Type,A.Type)] -> [A.Type]
    findDests _ [] = []
    findDests src ((dest,src'):ts) = if src == src' then dest : (findDests src ts) else findDests src ts

    --Listed in order (dest, src)
    --Signed numbers cannot be safely cast to unsigned numbers.  So (A.UInt16, A.Int8) isn't possible
    possibleConversions :: [(A.Type,A.Type)]
    possibleConversions
      = [
          (A.Byte, A.Bool)
          ,(A.Int8, A.Bool)

          ,(A.Int16, A.Int8)
          ,(A.Int16, A.Byte)
          ,(A.Int32, A.Int16)
          ,(A.Int32, A.UInt16)
          ,(A.Int64, A.Int32)
          ,(A.Int64, A.UInt32)

          ,(A.UInt16, A.Byte)
          ,(A.UInt32, A.UInt16)
          ,(A.UInt64, A.UInt32)
        ]




-- | Works out the least-general type that all given types can be upcast to.  Does not work with A.Int (as this function is expected only to be used by Rain)
-- As you would expect from the name, this function specifically follows the conversion rules for Rain.
leastGeneralSharedTypeRain :: [A.Type] -> Maybe A.Type
leastGeneralSharedTypeRain [] = Nothing
leastGeneralSharedTypeRain [t] = Just t
leastGeneralSharedTypeRain list@(t:ts)
  = if (all ((==) t) ts) then Just t else
      if (all isIntegerType list) then findInt list
      else Nothing
  where
    findInt :: [A.Type] -> Maybe A.Type
    findInt list = if null candidates
                     then Nothing
                     else Just $ snd $ maximumBy (comparing fst) candidates
                   where
                     candidates = if (all unsignedInt list) then (zip (map intSize list) list) else (allJustElseEmpty $ map findIntSigned list)

    signedInt :: A.Type -> Bool
    signedInt = not . unsignedInt

    unsignedInt :: A.Type -> Bool
    unsignedInt A.Byte = True
    unsignedInt A.UInt16 = True
    unsignedInt A.UInt32 = True
    unsignedInt A.UInt64 = True
    unsignedInt _ = False

    intSize :: A.Type -> Int
    intSize A.Byte = 1
    intSize A.UInt16 = 2
    intSize A.UInt32 = 4
    intSize A.UInt64 = 8
    intSize A.Int8 = 1
    intSize A.Int16 = 2
    intSize A.Int32 = 4
    intSize A.Int64 = 8
    intSize _ = 0 --should never happen

    --If all the items in the list are Just x, returns a list of them all.
    --If one (or more items) is Nothing, returns an empty list.
    allJustElseEmpty :: [Maybe a] -> [a]
    allJustElseEmpty ms = if (any isNothing ms) then [] else catMaybes ms

    --For each item in the list, get an ordered list of types we can cast to.
    findIntSigned :: A.Type -> Maybe (Int,A.Type)
    findIntSigned t = if (signedInt t)
                        then Just (intSize t,t)
                        --if it's unsigned, we need to cast it up by one type, assuming it's not already the biggest size
                        else transformMaybe (\x -> (intSize x,x)) (case t of
                               A.Byte -> Just A.Int16
                               A.UInt16 -> Just A.Int32
                               A.UInt32 -> Just A.Int64
                               A.UInt64 -> Nothing)

--{{{ classes of types
-- | Scalar integer types.
isIntegerType :: A.Type -> Bool
isIntegerType t
    = case t of
        A.Byte -> True
        A.UInt16 -> True
        A.UInt32 -> True
        A.UInt64 -> True
        A.Int8 -> True
        A.Int -> True
        A.Int16 -> True
        A.Int32 -> True
        A.Int64 -> True
        _ -> False

-- Real types.
isRealType :: A.Type -> Bool
isRealType t
    = case t of
        A.Real32 -> True
        A.Real64 -> True
        _ -> False

-- Types that are permitted as CASE selectors.
isCaseableType :: A.Type -> Bool
isCaseableType A.Bool = True
isCaseableType t = isIntegerType t
--}}}

--{{{ sizes of types
-- | The size in bytes of a data type.
data BytesInResult =
  BIJust Int            -- ^ Just that many bytes.
  | BIOneFree Int Int   -- ^ An array type; A bytes, times unknown dimension B.
  | BIManyFree          -- ^ An array type with multiple unknown dimensions.
  | BIUnknown           -- ^ We can't tell the size at compile time.
  deriving (Show, Eq)

-- | Return the size in bytes of a data type.
bytesInType :: (CSM m, Die m) => A.Type -> m BytesInResult
bytesInType A.Byte = return $ BIJust 1
bytesInType A.UInt16 = return $ BIJust 2
bytesInType A.UInt32 = return $ BIJust 4
bytesInType A.UInt64 = return $ BIJust 8
bytesInType A.Int8 = return $ BIJust 1
-- FIXME This is tied to the backend we're using (as is the constant folder).
bytesInType A.Int = return $ BIJust 4
bytesInType A.Int16 = return $ BIJust 2
bytesInType A.Int32 = return $ BIJust 4
bytesInType A.Int64 = return $ BIJust 8
bytesInType A.Real32 = return $ BIJust 4
bytesInType A.Real64 = return $ BIJust 8
bytesInType a@(A.Array _ _) = bytesInArray 0 a
  where
    bytesInArray :: (CSM m, Die m) => Int -> A.Type -> m BytesInResult
    bytesInArray num (A.Array [] t) = bytesInType t
    bytesInArray num (A.Array (d:ds) t)
        =  do ts <- bytesInArray (num + 1) (A.Array ds t)
              case (d, ts) of
                (A.Dimension n, BIJust m) -> return $ BIJust (n * m)
                (A.Dimension n, BIOneFree m x) -> return $ BIOneFree (n * m) x
                (A.UnknownDimension, BIJust m) -> return $ BIOneFree m num
                (A.UnknownDimension, BIOneFree _ _) -> return BIManyFree
                (_, _) -> return ts
bytesInType (A.Record n)
    =  do st <- specTypeOfName n
          case st of
            -- We can only do this for *packed* records -- for normal records,
            -- the compiler might insert padding.
            (A.RecordType _ True nts) -> bytesInList nts
            _ -> return $ BIUnknown
  where
    bytesInList :: (CSM m, Die m) => [(A.Name, A.Type)] -> m BytesInResult
    bytesInList [] = return $ BIJust 0
    bytesInList ((_, t):rest)
        =  do bi <- bytesInType t
              br <- bytesInList rest
              case (bi, br) of
                (BIJust a, BIJust b) -> return $ BIJust (a + b)
                (_, _) -> return BIUnknown
bytesInType _ = return $ BIUnknown
--}}}

-- | Get the number of items a replicator produces.
sizeOfReplicator :: A.Replicator -> A.Expression
sizeOfReplicator (A.For _ _ _ count) = count

-- | Get the number of items in a Structured as an expression.
sizeOfStructured :: A.Structured -> A.Expression
sizeOfStructured (A.Rep m rep s)
    = A.Dyadic m A.Times (sizeOfReplicator rep) (sizeOfStructured s)
sizeOfStructured (A.Spec _ _ s) = sizeOfStructured s
sizeOfStructured (A.ProcThen _ _ s) = sizeOfStructured s
sizeOfStructured (A.Several m ss)
    = case ss of
        [] -> makeConstant m 0
        _ -> foldl1 (A.Dyadic m A.Plus) (map sizeOfStructured ss)
sizeOfStructured s = makeConstant (findMeta s) 1

-- | Add one to an expression.
addOne :: A.Expression -> A.Expression
addOne e = A.Dyadic m A.Plus (makeConstant m 1) e
  where m = findMeta e

