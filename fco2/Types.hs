-- | Type inference and checking.
module Types where

import Control.Monad

import qualified AST as A
import ParseState

perhaps :: Maybe a -> (a -> b) -> Maybe b
perhaps m f = m >>= (Just . f)

-- FIXME: Eww, this shouldn't be necessary -- the lookups should really work on
-- Strings.
makeDummyName :: String -> A.Name
makeDummyName s = A.Name {
                    A.nameMeta = [],
                    A.nameType = A.ChannelName,
                    A.nameName = s
                  }

sameName :: A.Name -> A.Name -> Bool
sameName a b = A.nameName a == A.nameName b

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
        Just (A.IsChannel m t c) -> typeOfChannel ps c
        Just (A.IsChannelArray m t (c:_)) -> typeOfChannel ps c `perhaps` A.Array [A.UnknownDimension]
        Just (A.Retypes m am t v) -> Just t
        Just (A.RetypesExpr m am t e) -> Just t
        _ -> Nothing

-- FIXME: This should fail if the subscript is invalid...
subscriptType :: A.Type -> Maybe A.Type
subscriptType (A.Array [_] t) = Just t
subscriptType (A.Array (_:ds) t) = Just $ A.Array ds t
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
        A.ExprVariable m v -> typeOfVariable ps v
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

abbrevModeOfSpec :: A.SpecType -> A.AbbrevMode
abbrevModeOfSpec s
    = case s of
        A.Is _ am _ _ -> am
        A.IsExpr _ am _ _ -> am
        A.IsChannel _ _ _ -> A.Abbrev
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

