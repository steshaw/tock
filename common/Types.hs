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

-- | Type inference and checking.
module Types
  (
    specTypeOfName, typeOfSpec, typeOfSpec', abbrevModeOfName, underlyingType, stripArrayType, abbrevModeOfVariable, abbrevModeOfSpec
    , isRealType, isIntegerType, isNumericType, isCaseableType, isScalarType, isDataType, isCommunicableType, isSequenceType, isMobileType
    , resolveUserType, isSafeConversion, isPreciseConversion, isImplicitConversionRain
    , returnTypesOfFunction
    , BytesInResult(..), bytesInType, countReplicator, countStructured, computeStructured

    , makeAbbrevAM, makeConstant, makeDimension, specificDimSize, addOne, subOne, addExprs, subExprs,
      mulExprs, divExprs
    , addDimensions, applyDimension, removeFixedDimensions, trivialSubscriptType, subscriptType, unsubscriptType
    , applyDirection
    , recordFields, recordAttr, protocolItems, dirAttr

    , leastGeneralSharedTypeRain
    
    , ASTTypeable(..)
  ) where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe
import Data.List
import Data.Ord

import qualified AST as A
import CompState hiding (CSM) -- all these functions are read-only!
import Errors
import EvalLiterals
import Intrinsics
import Metadata
import PrettyShow
import ShowCode
import Traversal
import TypeSizes
import Utils

class ASTTypeable a where
  astTypeOf :: (CSMR m, Die m) => a -> m A.Type

instance ASTTypeable A.Type where
  astTypeOf = return

-- | Gets the 'A.SpecType' for a given 'A.Name' from the recorded types in the 'CompState'.  Dies with an error if the name is unknown.
specTypeOfName :: (CSMR m, Die m) => A.Name -> m A.SpecType
specTypeOfName n
    = liftM A.ndSpecType (lookupNameOrError n $ dieP (A.nameMeta n) $ "Could not find type in specTypeOfName for: " ++ (show $ A.nameName n))

-- | Gets the 'A.AbbrevMode' for a given 'A.Name' from the recorded types in the 'CompState'.  Dies with an error if the name is unknown.
abbrevModeOfName :: (CSMR m, Die m) => A.Name -> m A.AbbrevMode
abbrevModeOfName n
    = liftM A.ndAbbrevMode (lookupNameOrError n $ dieP (A.nameMeta n) $ "Could not find abbreviation mode in abbrevModeOfName for: " ++ (show $ A.nameName n))

instance ASTTypeable A.Name where
  astTypeOf = typeOfName

instance ASTTypeable A.Formal where
  astTypeOf (A.Formal _ t _) = return t

instance ASTTypeable A.Actual where
  astTypeOf (A.ActualVariable v) = astTypeOf v
  astTypeOf (A.ActualExpression e) = astTypeOf e
  astTypeOf (A.ActualClaim v)
              =  do t <- typeOfVariable v
                    case t of
                          A.Chan attr innerT -> return $ A.Chan (attr
                            { A.caWritingShared = A.Unshared
                            , A.caReadingShared = A.Unshared
                            }) innerT
                          A.ChanEnd A.DirInput _ innerT
                            -> return $ A.ChanEnd A.DirInput A.Unshared innerT
                          A.ChanEnd A.DirOutput _ innerT
                            -> return $ A.ChanEnd A.DirOutput A.Unshared innerT
                          A.ChanDataType dir _ innerT -> return $ A.ChanDataType dir A.Unshared innerT
                          _ -> dieP (findMeta v) "Item in claim not channel"
  astTypeOf (A.ActualChannelArray (v:vs))
    = do t <- typeOfVariable v
         return $ A.Array [A.Dimension $ makeConstant (findMeta v) (length vs+1)] t


-- | Gets the 'A.Type' for a given 'A.Name' by looking at its definition in the 'CompState'.  Dies with an error if the name is unknown.
typeOfName :: (CSMR m, Die m) => A.Name -> m A.Type
typeOfName n
    =  do st <- specTypeOfName n
          t <- typeOfSpec st
          case t of
            Just t' -> return t'
            Nothing -> dieP (findMeta n) $ "cannot type name " ++ pshow n ++
              ":" ++ show st

typeOfSpec' :: (CSMR m, Die m) => A.SpecType -> m (Maybe (A.Type, A.Type -> A.SpecType))
typeOfSpec' st
        = case st of
            A.Declaration a t -> return $ Just (t, A.Declaration a)
            A.Is a b t c -> return $ Just (t, \t' -> A.Is a b t' c)
            A.Retypes a b t c -> return $ Just (t, \t' -> A.Retypes a b t' c)
            A.RetypesExpr a b t c
              -> return $ Just (t, \t' -> A.RetypesExpr a b t' c)
            A.Rep _ (A.For _ _ e _) -> do t <- astTypeOf e
                                          return $ Just (t, error "typeOfSpec'")
            A.Rep _ (A.ForEach _ e) ->
              do t <- astTypeOf e
                 case t of
                   A.List t' -> return $ Just (t', error "typeOfSpec'")
                   A.Array _ t' -> return $ Just (t', error "typeOfSpec'")
                   _ -> return Nothing
            _ -> return Nothing

typeOfSpec :: (CSMR m, Die m) => A.SpecType -> m (Maybe A.Type)
typeOfSpec = liftM (fmap fst) . typeOfSpec'

--{{{  identifying types
-- | Get the fields of a record type.
recordFields :: (CSMR m, Die m) => Meta -> A.Type -> m [(A.Name, A.Type)]
recordFields m (A.Record rec)
    =  do st <- specTypeOfName rec
          case st of
            A.RecordType _ _ fs -> return fs
            _ -> dieP m "not record type"
recordFields m (A.ChanDataType A.DirInput _ n)
    =  do st <- specTypeOfName n
          case st of
            A.ChanBundleType _ _ fs -> return fs
            _ -> dieP m "not record type"
-- Directions are flipped for the ! end:
recordFields m (A.ChanDataType A.DirOutput _ n)
    =  do st <- specTypeOfName n
          case st of
            A.ChanBundleType _ _ fs -> return [(n, flipDirOfEnd t) | (n, t) <- fs]
            _ -> dieP m "not record type"
  where
    flipDirOfEnd (A.ChanEnd dir attr t) = A.ChanEnd (flipDir dir) attr t
    flipDir A.DirInput = A.DirOutput
    flipDir A.DirOutput = A.DirInput
recordFields m _ = dieP m "not record type"

recordAttr :: (CSMR m, Die m) => Meta -> A.Type -> m A.RecordAttr
recordAttr m (A.Record rec)
    =  do st <- specTypeOfName rec
          case st of
            A.RecordType _ attr _ -> return attr
            _ -> dieP m "not record type"
recordAttr m _ = dieP m "not record type"

dirAttr :: A.Direction -> A.ChanAttributes -> A.ShareMode
dirAttr A.DirInput = A.caReadingShared
dirAttr A.DirOutput = A.caWritingShared

-- | Get the type of a record field.
typeOfRecordField :: (CSMR m, Die m) => Meta -> A.Type -> A.Name -> m A.Type
typeOfRecordField m t field
    =  do fs <- recordFields m t
          checkJust (Just m, "unknown record field") $ lookup field fs

-- | Apply a plain subscript to a type.
plainSubscriptType :: (CSMR m, Die m) => Meta -> A.Type -> m A.Type
plainSubscriptType m (A.Array (_:ds) t)
    = return $ case ds of
                 [] -> t
                 _ -> A.Array ds t
plainSubscriptType m (A.Mobile t) = plainSubscriptType m t
plainSubscriptType m t = diePC m $ formatCode "Subscript of non-array type: %" t

-- | Turn an expression into a 'Dimension'.
-- If the expression is constant, it'll produce 'Dimension'; if not, it'll
-- produce 'UnknownDimension'.
dimensionFromExpr :: A.Expression -> A.Dimension
dimensionFromExpr e
    = if isConstant e
        then A.Dimension $ e
        else A.UnknownDimension

-- | Apply a subscript to a type, and return what the type is after it's been
-- subscripted.
subscriptType :: (CSMR m, Die m) => A.Subscript -> A.Type -> m A.Type
subscriptType sub A.Infer
    = return $ A.Infer
subscriptType sub t@(A.UserDataType _)
    = resolveUserType (findMeta sub) t >>= subscriptType sub
subscriptType (A.SubscriptFromFor m _ _ count) (A.Array (_:ds) t)
    = return $ A.Array (dimensionFromExpr count : ds) t
subscriptType (A.SubscriptFrom m _ base) (A.Array (d:ds) t)
    = return $ A.Array (dim : ds) t
  where
    dim = case d of
            A.Dimension size -> dimensionFromExpr $ A.Dyadic m A.Subtr size base
            _ -> A.UnknownDimension
subscriptType (A.SubscriptFor m _ count) (A.Array (_:ds) t)
    = return $ A.Array (dimensionFromExpr count : ds) t
subscriptType (A.SubscriptField m tag) t = typeOfRecordField m t tag
subscriptType (A.Subscript m _ _) t = plainSubscriptType m t
subscriptType sub t = diePC (findMeta sub) $ formatCode "Unsubscriptable type: %" t

-- | The inverse of 'subscriptType': given a type that we know is the result of
-- a subscript, return what the type being subscripted is.
unsubscriptType :: (CSMR m, Die m) => A.Subscript -> A.Type -> m A.Type
unsubscriptType _ A.Infer
    = return $ A.Infer
unsubscriptType (A.SubscriptFromFor _ _ _ _) t
    = return $ removeFixedDimension t
unsubscriptType (A.SubscriptFrom _ _ _) t
    = return $ removeFixedDimension t
unsubscriptType (A.SubscriptFor _ _ _) t
    = return $ removeFixedDimension t
unsubscriptType (A.SubscriptField m _) t
    = dieP m $ "unsubscript of record type (but we can't tell which one)"
unsubscriptType (A.Subscript _ _ sub) t
    = return $ addDimensions [A.UnknownDimension] t

-- | Just remove the first dimension from an array type -- like doing
-- subscriptType with constant 0 as a subscript, but without the checking.
-- This is used for the couple of cases where we know it's safe and don't want
-- the usage check.
trivialSubscriptType :: (CSMR m, Die m) => Meta -> A.Type -> m A.Type
trivialSubscriptType _ A.Infer = return A.Infer
trivialSubscriptType m t@(A.UserDataType _)
    = resolveUserType m t >>= trivialSubscriptType m
trivialSubscriptType _ (A.Array [d] t) = return t
trivialSubscriptType _ (A.Array (d:ds) t) = return $ A.Array ds t
trivialSubscriptType m (A.Mobile t) = trivialSubscriptType m t
trivialSubscriptType m t = diePC m $ formatCode "not plain array type: %" t

instance ASTTypeable A.Variable where
  astTypeOf = typeOfVariable

-- | Gets the 'A.Type' of a 'A.Variable' by looking at the types recorded in the 'CompState'.
typeOfVariable :: (CSMR m, Die m) => A.Variable -> m A.Type
typeOfVariable (A.Variable m n) = typeOfName n
typeOfVariable (A.SubscriptedVariable m s v)
    = typeOfVariable v >>= subscriptType s
typeOfVariable (A.DerefVariable m v)
    = do t <- typeOfVariable v
         case t of
           A.Mobile innerT -> return innerT
           _ -> dieP m $ "Dereference applied to non-mobile variable"
typeOfVariable (A.DirectedVariable m dir v)
    = do t <- typeOfVariable v
         case t of
           A.ChanEnd dir' _ _ ->
             if dir == dir'
               then return t
               else dieP m $ "Attempted to reverse direction of a channel-end"
           A.Chan attr innerT -> return $ A.ChanEnd dir (dirAttr dir attr) innerT
           A.Array ds (A.Chan attr innerT)
             -> return $ A.Array ds (A.ChanEnd dir (dirAttr dir attr) innerT)
           A.Array _ (A.ChanEnd dir' _ _) ->
             if dir == dir'
               then return t
               else dieP m $ "Attempted to reverse direction of a channel-end"
           A.Infer -> return $ A.ChanEnd dir A.Unshared A.Infer
           _ -> diePC m $ formatCode "Direction specified on non-channel variable of type: %" t
typeOfVariable (A.VariableSizes m v)
  = do t <- typeOfVariable v
       case t of
         A.Array ds _ -> return $ A.Array [A.Dimension $ makeConstant m $ length ds] A.Int
         _ -> diePC m $ formatCode "Attempted to get size of non-array: % (type: %)" v t

-- | Get the abbreviation mode of a variable.
abbrevModeOfVariable :: (CSMR m, Die m) => A.Variable -> m A.AbbrevMode
abbrevModeOfVariable (A.Variable _ n) = abbrevModeOfName n
abbrevModeOfVariable (A.SubscriptedVariable _ sub v) = abbrevModeOfVariable v
abbrevModeOfVariable (A.DirectedVariable _ _ v) = abbrevModeOfVariable v
abbrevModeOfVariable (A.DerefVariable _ v) = return A.Original
abbrevModeOfVariable (A.VariableSizes {}) = return A.Original

dyadicIsBoolean :: A.DyadicOp -> Bool
dyadicIsBoolean A.Eq = True
dyadicIsBoolean A.NotEq = True
dyadicIsBoolean A.Less = True
dyadicIsBoolean A.More = True
dyadicIsBoolean A.LessEq = True
dyadicIsBoolean A.MoreEq = True
dyadicIsBoolean A.After = True
dyadicIsBoolean _ = False

instance ASTTypeable A.Expression where
  astTypeOf = typeOfExpression

-- | Gets the 'A.Type' of an 'A.Expression'.  This function assumes that the expression has already been type-checked.
typeOfExpression :: (CSMR m, Die m) => A.Expression -> m A.Type
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
        A.Conversion m cm t e -> return t
        A.ExprVariable m v -> typeOfVariable v
        A.Literal _ t _ -> return t
        A.True m -> return A.Bool
        A.False m -> return A.Bool
        A.FunctionCall m n es -> liftM head $ returnTypesOfFunction n
        A.IntrinsicFunctionCall m s _ -> liftM head $ returnTypesOfIntrinsic m s
        A.SubscriptedExpr m s e ->
          typeOfExpression e >>= subscriptType s
        A.BytesInExpr m e -> return A.Int
        A.BytesInType m t -> return A.Int
        A.OffsetOf m t n -> return A.Int
        A.AllocMobile _ t _ -> return t
        A.CloneMobile _ e -> typeOfExpression e
        A.IsDefined {} -> return A.Bool
--}}}

-- | Gets the return type(s) of a function call from the 'CompState'.
returnTypesOfFunction :: (CSMR m, Die m) => A.Name -> m [A.Type]
returnTypesOfFunction n
    =  do st <- specTypeOfName n
          case st of
            A.Function _ _ rs _ _ -> return rs
            -- If it's not defined as a function, it might have been converted to a proc.
            _ ->
              do ps <- getCompState
                 checkJust (Just $ findMeta n, "not defined as a function") $
                   Map.lookup (A.nameName n) (csFunctionReturns ps)

returnTypesOfIntrinsic :: (CSMR m, Die m) => Meta -> String -> m [A.Type]
returnTypesOfIntrinsic m s
 = do frontend <- getCompState >>* csFrontend
      let intrinsicList = case frontend of
            FrontendOccam -> intrinsicFunctions
            FrontendRain -> rainIntrinsicFunctions
      case lookup s intrinsicList of
        Just (rts, _) -> return rts
        Nothing -> dieP m $ "unknown intrinsic function " ++ s

-- | Get the items in a channel's protocol (for typechecking).
-- Returns Left if it's a simple protocol, Right if it's tagged.
protocolItems :: (CSMR m, Die m) => A.Variable -> m (Either [A.Type] [(A.Name, [A.Type])])
protocolItems v
    =  do chanT <- typeOfVariable v
          t <- case chanT of
                 A.Chan _ t -> return t
                 A.ChanEnd _ _ t -> return t
                 _ -> dieP (findMeta v) $ "Expected a channel variable, but this is of type: " ++ show chanT
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
        A.Retypes _ am _ _ -> am
        A.RetypesExpr _ am _ _ -> am
        _ -> A.Original

-- | Resolve a datatype into its underlying type -- i.e. if it's a named data
-- type, then return the underlying real type. This will recurse.
underlyingType :: forall m. (CSMR m, Die m) => Meta -> A.Type -> m A.Type
underlyingType m = applyDepthM doType
  where
    doType :: A.Type -> m A.Type
    -- This is fairly subtle: after resolving a user type, we have to recurse
    -- on the resulting type.
    doType t@(A.UserDataType _) = resolveUserType m t >>= underlyingType m
    doType t = return t

-- | Like underlyingType, but only do the "outer layer": if you give this a
-- user type that's an array of user types, then you'll get back an array of
-- user types.
resolveUserType :: (CSMR m, Die m) => Meta -> A.Type -> m A.Type
resolveUserType m (A.UserDataType n)
    =  do st <- specTypeOfName n
          case st of
            A.DataType _ t -> resolveUserType m t
            _ -> dieP m $ "Not a type name: " ++ show n
resolveUserType _ t = return t

-- | Add array dimensions to a type; if it's already an array it'll just add
-- the new dimensions to the existing array.
addDimensions :: [A.Dimension] -> A.Type -> A.Type
addDimensions newDs (A.Array ds t) = A.Array (newDs ++ ds) t
addDimensions ds t = A.Array ds t

-- | Set the first dimension of an array type.
applyDimension :: A.Dimension -> A.Type -> A.Type
applyDimension dim (A.Array (_:ds) t) = A.Array (dim : ds) t
applyDimension _ t = t

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

-- | Generate a constant expression from an integer -- for array sizes and the
-- like.
makeConstant :: Meta -> Int -> A.Expression
makeConstant m n = A.Literal m A.Int $ A.IntLiteral m (show n)

-- | Generate a constant dimension from an integer.
makeDimension :: Meta -> Int -> A.Dimension
makeDimension m n = A.Dimension $ makeConstant m n

-- | Apply a direction to a type.
applyDirection :: Die m => Meta -> A.Direction -> A.Type -> m A.Type
applyDirection m dir (A.Array ds t)
    = applyDirection m dir t >>* A.Array ds
applyDirection m dir (A.Chan ca t)
    = return $ A.ChanEnd dir (dirAttr dir ca) t
applyDirection m _ t
    = dieP m "Direction specified on non-channel type"

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
        A.Time -> True
        _ -> False

-- | Scalar real types.
isRealType :: A.Type -> Bool
isRealType t
    = case t of
        A.Real32 -> True
        A.Real64 -> True
        _ -> False

-- | Numeric types.
isNumericType :: A.Type -> Bool
isNumericType t = isIntegerType t || isRealType t

-- | Types that are permitted as 'Case' selectors.
isCaseableType :: A.Type -> Bool
isCaseableType A.Bool = True
isCaseableType t = isIntegerType t

-- | All scalar types.
isScalarType :: A.Type -> Bool
isScalarType A.Bool = True
isScalarType t = isIntegerType t || isRealType t

-- | Types that can be used to define 'DataType's.
isDataType :: A.Type -> Bool
-- This may change in the future.
isDataType = isCommunicableType

-- | Types that can be communicated across a channel.
isCommunicableType :: A.Type -> Bool
isCommunicableType (A.Array _ t) = isCommunicableType t
isCommunicableType (A.List t) = isCommunicableType t
isCommunicableType (A.Record _) = True
isCommunicableType (A.Mobile _) = True
isCommunicableType t = isScalarType t

-- | Types that support 'Size' and subscripting.
isSequenceType :: Bool -> A.Type -> Bool
isSequenceType _ (A.Array _ _) = True
isSequenceType _ (A.List _) = True
isSequenceType True (A.Mobile t) = isSequenceType False t
isSequenceType _ _ = False

isMobileType :: (CSMR m, Die m) => A.Type -> m Bool
isMobileType (A.Mobile {}) = return True
isMobileType t@(A.Record n) = recordAttr (A.nameMeta n) t >>* A.mobileRecord
isMobileType (A.ChanDataType {}) = return True
isMobileType _ = return False

--}}}

--{{{ sizes of types
-- | The size in bytes of a data type.
data BytesInResult =
  BIJust A.Expression          -- ^ Just that many bytes.
  | BIOneFree A.Expression Int -- ^ An array type; A bytes, times unknown dimension B.
  | BIManyFree                 -- ^ An array type with multiple unknown dimensions.
  | BIUnknown                  -- ^ We can't tell the size at compile time.
  deriving (Show, Eq)

-- | Make a fixed-size 'BytesInResult'.
justSize :: CSMR m => Int -> m BytesInResult
justSize n = return $ BIJust $ makeConstant emptyMeta n

-- | Given the C and C++ values (in that order), selects according to the
-- backend. If the backend is not recognised, the C sizes are used.
justSizeBackends :: CSMR m => Int -> Int -> m BytesInResult
justSizeBackends c cxx
    =  do backend <- getCompState >>* csBackend
          case backend of
            BackendCPPCSP -> justSize c
            _ -> justSize cxx

-- | Return the size in bytes of a data type.
bytesInType :: (CSMR m, Die m) => A.Type -> m BytesInResult
bytesInType A.Bool = justSizeBackends cBoolSize cxxBoolSize
bytesInType A.Byte = justSize 1
bytesInType A.UInt16 = justSize 2
bytesInType A.UInt32 = justSize 4
bytesInType A.UInt64 = justSize 8
bytesInType A.Int8 = justSize 1
bytesInType A.Int = justSizeBackends cIntSize cxxIntSize
bytesInType A.Int16 = justSize 2
bytesInType A.Int32 = justSize 4
bytesInType A.Int64 = justSize 8
bytesInType A.Real32 = justSize 4
bytesInType A.Real64 = justSize 8
bytesInType a@(A.Array _ _) = bytesInArray 0 a
  where
    bytesInArray :: (CSMR m, Die m) => Int -> A.Type -> m BytesInResult
    bytesInArray num (A.Array [] t) = bytesInType t
    bytesInArray num (A.Array (d:ds) t)
        =  do ts <- bytesInArray (num + 1) (A.Array ds t)
              case (d, ts) of
                (A.Dimension n, BIJust m) -> return $ BIJust (mulExprs n m)
                (A.Dimension n, BIOneFree m x) -> return $ BIOneFree (mulExprs n m) x
                (A.UnknownDimension, BIJust m) -> return $ BIOneFree m num
                (A.UnknownDimension, BIOneFree _ _) -> return BIManyFree
                (_, _) -> return ts
bytesInType (A.Record n)
    =  do st <- specTypeOfName n
          case st of
            -- We can only do this for *packed* records -- for normal records,
            -- the compiler might insert padding.
            (A.RecordType _ (A.RecordAttr {A.packedRecord=True}) nts) -> bytesInList nts
            _ -> return $ BIUnknown
  where
    bytesInList :: (CSMR m, Die m) => [(A.Name, A.Type)] -> m BytesInResult
    bytesInList [] = justSize 0
    bytesInList ((_, t):rest)
        =  do bi <- bytesInType t
              br <- bytesInList rest
              case (bi, br) of
                (BIJust a, BIJust b) -> return $ BIJust (addExprs a b)
                (_, _) -> return BIUnknown
bytesInType _ = return $ BIUnknown
--}}}

-- | Get the number of items a replicator produces.
countReplicator :: A.Replicator -> A.Expression
countReplicator (A.For _ _ count _) = count

-- | Get the number of items in a Structured as an expression.
countStructured :: Data a => A.Structured a -> A.Expression
countStructured = computeStructured (\m _ -> makeConstant m 1)

-- | Compute an expression over a Structured.
computeStructured :: Data a => (Meta -> a -> A.Expression) -> A.Structured a -> A.Expression
computeStructured f (A.Spec _ (A.Specification _ _ (A.Rep m rep)) s)
    = A.Dyadic m A.Times (countReplicator rep) (computeStructured f s)
computeStructured f (A.Spec _ _ s) = computeStructured f s
computeStructured f (A.ProcThen _ _ s) = computeStructured f s
computeStructured f (A.Only m x) = f m x
computeStructured f (A.Several m ss)
    = case ss of
        [] -> makeConstant m 0
        _ -> foldl1 (A.Dyadic m A.Plus) (map (computeStructured f) ss)

specificDimSize :: Int -> A.Variable -> A.Variable
specificDimSize n v = A.SubscriptedVariable (findMeta v) (A.Subscript (findMeta v) A.NoCheck
  $ makeConstant (findMeta v) n) $ A.VariableSizes (findMeta v) v


-- | Add one to an expression.
addOne :: A.Expression -> A.Expression
addOne e = A.Dyadic m A.Add (makeConstant m 1) e
  where m = findMeta e

-- | Subtrace one from an expression.
subOne :: A.Expression -> A.Expression
subOne e = A.Dyadic m A.Subtr e (makeConstant m 1)
  where m = findMeta e

-- | Add two expressions.
addExprs :: A.Expression -> A.Expression -> A.Expression
addExprs a b = A.Dyadic m A.Add a b
  where m = findMeta a

-- | Add two expressions.
subExprs :: A.Expression -> A.Expression -> A.Expression
subExprs a b = A.Dyadic m A.Subtr a b
  where m = findMeta a

-- | Multiply two expressions.
mulExprs :: A.Expression -> A.Expression -> A.Expression
mulExprs a b = A.Dyadic m A.Mul a b
  where m = findMeta a

-- | Divide two expressions.
divExprs :: A.Expression -> A.Expression -> A.Expression
divExprs a b = A.Dyadic m A.Div a b
  where m = findMeta a
