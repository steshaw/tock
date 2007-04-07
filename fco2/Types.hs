module Types where

import qualified AST as A
import ParseState

-- I'm pretty sure this is in the standard library, but I can't find it!
perhapsM :: Maybe a -> (a -> Maybe b) -> Maybe b
perhapsM m f
    = case m of
        Just v -> f v
        _ -> Nothing

perhaps :: Maybe a -> (a -> b) -> Maybe b
perhaps m f = m `perhapsM` (Just . f)

specTypeOfName :: ParseState -> A.Name -> Maybe A.SpecType
specTypeOfName ps n
    = (psLookupName ps n) `perhaps` A.ndType

typeOfName :: ParseState -> A.Name -> Maybe A.Type
typeOfName ps n
    = case specTypeOfName ps n of
        Just (A.Declaration m t) -> Just t
        Just (A.Is m t v) -> typeOfVariable ps v
        Just (A.ValIs m t e) -> typeOfExpression ps e `perhaps` A.Val
        Just (A.IsChannel m t c) -> typeOfChannel ps c
        Just (A.IsChannelArray m t (c:_)) -> typeOfChannel ps c `perhaps` A.ArrayUnsized
        Just (A.Retypes m t v) -> Just t
        Just (A.Reshapes m t v) -> Just t
        Just (A.ValRetypes m t v) -> Just (A.Val t)
        Just (A.ValReshapes m t v) -> Just (A.Val t)
        _ -> Nothing

-- FIXME: This should fail if the subscript is invalid...
subscriptType :: A.Type -> Maybe A.Type
subscriptType (A.Val t) = subscriptType t `perhaps` A.Val
subscriptType (A.Array e t) = Just t
subscriptType (A.ArrayUnsized t) = Just t
subscriptType _ = Nothing

typeOfChannel :: ParseState -> A.Channel -> Maybe A.Type
typeOfChannel ps (A.Channel m n) = typeOfName ps n
typeOfChannel ps (A.SubscriptedChannel m s c)
    = typeOfChannel ps c >>= subscriptType

typeOfVariable :: ParseState -> A.Variable -> Maybe A.Type
typeOfVariable ps (A.Variable m n) = typeOfName ps n
typeOfVariable ps (A.SubscriptedVariable m s v)
    = typeOfVariable ps v >>= subscriptType

typeOfExpression :: ParseState -> A.Expression -> Maybe A.Type
typeOfExpression ps e
    = case e of
        A.Monadic m op e -> typeOfExpression ps e
        A.Dyadic m op e f -> typeOfExpression ps e   -- assume f's been checked!
        A.MostPos m t -> Just t
        A.MostNeg m t -> Just t
        A.Size m t -> Just A.Int
        A.Conversion m cm t e -> Just t
        A.ExprVariable m v -> typeOfVariable ps v `perhaps` noVal
        A.ExprLiteral m l -> typeOfLiteral ps l
        A.True m -> Just A.Bool
        A.False m -> Just A.Bool
        A.FunctionCall m n es
            -> case returnTypesOfFunction ps n of
                 Just [t] -> Just t
                 _ -> Nothing
        A.SubscriptedExpr m s e
            -> typeOfExpression ps e >>= subscriptType
        A.BytesInExpr m e -> Just A.Int
        A.BytesInType m t -> Just A.Int
        A.OffsetOf m t n -> Just A.Int

typeOfLiteral :: ParseState -> A.Literal -> Maybe A.Type
typeOfLiteral ps (A.Literal m t lr) = Just t
typeOfLiteral ps (A.SubscriptedLiteral m s l)
    = typeOfLiteral ps l >>= subscriptType

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

noVal :: A.Type -> A.Type
noVal (A.Val t) = t
noVal t = t

