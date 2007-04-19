-- | Type inference and checking.
module Types where

-- FIXME: This module is a mess -- sort it and document the functions.

-- FIXME: These functions should have state-monadic versions.
-- It'd be nice if we could provide an instance of StateMonad for the Parsec state...

import Control.Monad
import Data.Maybe

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

--{{{  identifying types
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
abbrevModeOfVariable ps (A.SubscriptedVariable _ sub v)
    =  do am <- abbrevModeOfVariable ps v
          return $ case (am, sub) of
                     (A.ValAbbrev, A.Subscript _ _) -> A.ValAbbrev
                     (_, A.Subscript _ _) -> A.Original
                     (A.ValAbbrev, A.SubscriptField _ _) -> A.ValAbbrev
                     (_, A.SubscriptField _ _) -> A.Original
                     _ -> am

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
--}}}

--{{{  identifying constants
-- | Can an expression's value be determined at compile time?
isConstExpression :: ParseState -> A.Expression -> Bool
isConstExpression ps e
    = case e of
        A.Monadic m op e -> isConstExpression ps e
        A.Dyadic m op e f ->
          isConstExpression ps e && isConstExpression ps f
        A.MostPos m t -> True
        A.MostNeg m t -> True
        A.SizeType m t -> True
        A.SizeExpr m e -> isConstExpression ps e
        A.Conversion m cm t e -> isConstExpression ps e
        A.ExprVariable m v -> isConstVariable ps v
        A.ExprLiteral m l -> isConstLiteral ps l
        A.True m -> True
        A.False m -> True
        -- This could be true if we could identify functions with constant
        -- arguments and evaluate them at compile time, but I don't think we
        -- really want to go there...
        A.FunctionCall m n es -> False
        A.SubscriptedExpr m s e ->
          isConstSubscript ps s && isConstExpression ps e
        A.BytesInExpr m e -> isConstExpression ps e
        A.BytesInType m t -> True
        A.OffsetOf m t n -> True

-- | Can an literal's value be determined at compile time?
-- (Don't laugh -- array literals can't always!)
isConstLiteral :: ParseState -> A.Literal -> Bool
isConstLiteral ps (A.Literal _ _ lr) = isConstLiteralRepr ps lr
isConstLiteral ps (A.SubscriptedLiteral _ s l)
    = isConstSubscript ps s && isConstLiteral ps l

isConstLiteralRepr :: ParseState -> A.LiteralRepr -> Bool
isConstLiteralRepr ps (A.ArrayLiteral _ es)
    = and [isConstExpression ps e | e <- es]
isConstLiteralRepr _ _ = True

-- | Can a variable's value be determined at compile time?
isConstVariable :: ParseState -> A.Variable -> Bool
isConstVariable ps (A.Variable _ n) = isConstName ps n
isConstVariable ps (A.SubscriptedVariable _ s v)
    = isConstSubscript ps s && isConstVariable ps v

-- | Does a name refer to a constant variable?
isConstName :: ParseState -> A.Name -> Bool
isConstName ps n = isConstSpecType ps $ fromJust $ specTypeOfName ps n

-- | Can a specification's value (that is, the value of a variable defined
-- using that specification) be determined at compile time?
isConstSpecType :: ParseState -> A.SpecType -> Bool
isConstSpecType ps (A.Is _ _ _ v) = isConstVariable ps v
isConstSpecType ps (A.IsExpr _ _ _ e) = isConstExpression ps e
isConstSpecType ps (A.Retypes _ _ _ v) = isConstVariable ps v
isConstSpecType ps (A.RetypesExpr _ _ _ e) = isConstExpression ps e
isConstSpecType _ _ = False

-- | Can a subscript's value (that is, the range of subscripts it extracts) be
-- determined at compile time?
isConstSubscript :: ParseState -> A.Subscript -> Bool
isConstSubscript ps (A.Subscript _ e) = isConstExpression ps e
isConstSubscript ps (A.SubscriptField _ _) = True
isConstSubscript ps (A.SubscriptFromFor _ e f)
    = isConstExpression ps e && isConstExpression ps f
isConstSubscript ps (A.SubscriptFrom _ e) = isConstExpression ps e
isConstSubscript ps (A.SubscriptFor _ e) = isConstExpression ps e
--}}}

returnTypesOfFunction :: ParseState -> A.Name -> Maybe [A.Type]
returnTypesOfFunction ps n
    = case specTypeOfName ps n of
        Just (A.Function m rs fs vp) -> Just rs
        -- If it's not defined as a function, it might have been converted to a proc.
        _ -> lookup (A.nameName n) (psFunctionReturns ps)

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
