-- | Type inference and checking.
module Types where

-- FIXME: This module is a mess -- sort it and document the functions.

-- FIXME: These functions should have state-monadic versions.
-- It'd be nice if we could provide an instance of StateMonad for the Parsec state...

import Control.Monad

import qualified AST as A
import ParseState
import Metadata

perhaps :: Maybe a -> (a -> b) -> Maybe b
perhaps m f = m >>= (Just . f)

specTypeOfName :: ParseState -> A.Name -> Maybe A.SpecType
specTypeOfName ps n
    = (psLookupName ps n) `perhaps` A.ndType

abbrevModeOfName :: ParseState -> A.Name -> Maybe A.AbbrevMode
abbrevModeOfName ps n
    = (psLookupName ps n) `perhaps` A.ndAbbrevMode

typeOfName :: ParseState -> A.Name -> Maybe A.Type
typeOfName ps n
    = case specTypeOfName ps n of
        Just (A.Declaration m t) -> Just t
        Just (A.Is m am t v) -> typeOfVariable ps v
        Just (A.IsExpr m am t e) -> typeOfExpression ps e
        Just (A.IsChannelArray m t (c:_)) -> typeOfVariable ps c `perhaps` A.Array [A.UnknownDimension]
        Just (A.Retypes m am t v) -> Just t
        Just (A.RetypesExpr m am t e) -> Just t
        _ -> Nothing

typeOfRecordField :: ParseState -> A.Type -> A.Name -> Maybe A.Type
typeOfRecordField ps (A.UserDataType rec) field
    =  do st <- specTypeOfName ps rec
          case st of
            A.DataTypeRecord _ _ fs -> lookup field fs
            _ -> Nothing
typeOfRecordField _ _ _ = Nothing

subscriptType :: ParseState -> A.Subscript -> A.Type -> Maybe A.Type
subscriptType _ (A.SubscriptFromFor _ _ _) t = Just t
subscriptType _ (A.SubscriptFrom _ _) t = Just t
subscriptType _ (A.SubscriptFor _ _) t = Just t
subscriptType ps (A.SubscriptField _ tag) t = typeOfRecordField ps t tag
subscriptType _ (A.Subscript _ _) (A.Array [_] t) = Just t
subscriptType _ (A.Subscript _ _) (A.Array (_:ds) t) = Just $ A.Array ds t
subscriptType _ _ _ = Nothing

typeOfVariable :: ParseState -> A.Variable -> Maybe A.Type
typeOfVariable ps (A.Variable m n) = typeOfName ps n
typeOfVariable ps (A.SubscriptedVariable m s v)
    = typeOfVariable ps v >>= subscriptType ps s

abbrevModeOfVariable :: ParseState -> A.Variable -> Maybe A.AbbrevMode
abbrevModeOfVariable ps (A.Variable _ n) = abbrevModeOfName ps n
abbrevModeOfVariable ps (A.SubscriptedVariable _ _ v) = abbrevModeOfVariable ps v

dyadicIsBoolean :: A.DyadicOp -> Bool
dyadicIsBoolean A.Eq = True
dyadicIsBoolean A.NotEq = True
dyadicIsBoolean A.Less = True
dyadicIsBoolean A.More = True
dyadicIsBoolean A.LessEq = True
dyadicIsBoolean A.MoreEq = True
dyadicIsBoolean A.After = True
dyadicIsBoolean _ = False

typeOfExpression :: ParseState -> A.Expression -> Maybe A.Type
typeOfExpression ps e
    = case e of
        A.Monadic m op e -> typeOfExpression ps e
        A.Dyadic m op e f ->
          if dyadicIsBoolean op then Just A.Bool else typeOfExpression ps e
        A.MostPos m t -> Just t
        A.MostNeg m t -> Just t
        A.SizeType m t -> Just A.Int
        A.SizeExpr m t -> Just A.Int
        A.Conversion m cm t e -> Just t
        A.ExprVariable m v -> typeOfVariable ps v
        A.ExprLiteral m l -> typeOfLiteral ps l
        A.True m -> Just A.Bool
        A.False m -> Just A.Bool
        A.FunctionCall m n es ->
          case returnTypesOfFunction ps n of
            Just [t] -> Just t
            _ -> Nothing
        A.SubscriptedExpr m s e ->
          typeOfExpression ps e >>= subscriptType ps s
        A.BytesInExpr m e -> Just A.Int
        A.BytesInType m t -> Just A.Int
        A.OffsetOf m t n -> Just A.Int

typeOfLiteral :: ParseState -> A.Literal -> Maybe A.Type
typeOfLiteral ps (A.Literal m t lr) = Just t
typeOfLiteral ps (A.SubscriptedLiteral m s l)
    = typeOfLiteral ps l >>= subscriptType ps s

returnTypesOfFunction :: ParseState -> A.Name -> Maybe [A.Type]
returnTypesOfFunction ps n
    = case specTypeOfName ps n of
        Just (A.Function m rs fs vp) -> Just rs
        _ -> Nothing

isCaseProtocolType :: ParseState -> A.Type -> Bool
isCaseProtocolType ps (A.Chan (A.UserProtocol pr))
    = case specTypeOfName ps pr of
        Just (A.ProtocolCase _ _) -> True
        _ -> False
isCaseProtocolType ps _ = False

abbrevModeOfSpec :: A.SpecType -> A.AbbrevMode
abbrevModeOfSpec s
    = case s of
        A.Is _ am _ _ -> am
        A.IsExpr _ am _ _ -> am
        A.IsChannelArray _ _ _ -> A.Abbrev
        A.Retypes _ am _ _ -> am
        A.RetypesExpr _ am _ _ -> am
        _ -> A.Original

-- | Add an array dimension to a type; if it's already an array it'll just add
-- a new dimension to the existing array.
makeArrayType :: A.Dimension -> A.Type -> A.Type
makeArrayType d (A.Array ds t) = A.Array (d : ds) t
makeArrayType d t = A.Array [d] t

isChannelType :: A.Type -> Bool
isChannelType (A.Array _ t) = isChannelType t
isChannelType (A.Chan _) = True
isChannelType _ = False

stripArrayType :: A.Type -> A.Type
stripArrayType (A.Array _ t) = stripArrayType t
stripArrayType t = t

-- | Generate a constant expression from an integer -- for array sizes and the like.
makeConstant :: Meta -> Int -> A.Expression
makeConstant m n = A.ExprLiteral m $ A.Literal m A.Int $ A.IntLiteral m (show n)
