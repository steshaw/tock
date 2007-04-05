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
subscriptType (A.Array e t) = Just t
subscriptType (A.ArrayUnsized t) = Just t
subscriptType _ = Nothing

typeOfChannel :: ParseState -> A.Channel -> Maybe A.Type
typeOfChannel ps (A.Channel m n) = typeOfName ps n
typeOfChannel ps (A.SubscriptedChannel m s c)
    = case typeOfChannel ps c of
        Just t -> subscriptType t
        _ -> Nothing

typeOfVariable :: ParseState -> A.Variable -> Maybe A.Type
typeOfVariable ps v = Nothing

typeOfExpression :: ParseState -> A.Expression -> Maybe A.Type
typeOfExpression ps e = Nothing

isCaseProtocolType :: ParseState -> A.Type -> Bool
isCaseProtocolType ps (A.Chan (A.UserProtocol pr))
    = case specTypeOfName ps pr of
        Just (A.ProtocolCase _ _) -> True
        _ -> False
isCaseProtocolType ps _ = False

