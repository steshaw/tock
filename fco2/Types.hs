-- | Type inference and checking.
module Types where

-- FIXME: This module is a mess -- sort it and document the functions.

import Control.Monad
import Control.Monad.State
import Data.Generics
import Data.Maybe

import qualified AST as A
import Errors
import ParseState
import Metadata

specTypeOfName :: (PSM m, Die m) => A.Name -> m A.SpecType
specTypeOfName n
    = liftM A.ndType (lookupName n)

abbrevModeOfName :: (PSM m, Die m) => A.Name -> m A.AbbrevMode
abbrevModeOfName n
    = liftM A.ndAbbrevMode (lookupName n)

typeOfName :: (PSM m, Die m) => A.Name -> m A.Type
typeOfName n
    =  do st <- specTypeOfName n
          case st of
            A.Declaration _ t -> return t
            A.Is _ _ _ v -> typeOfVariable v
            A.IsExpr _ _ _ e -> typeOfExpression e
            A.IsChannelArray _ _ (c:_) -> liftM (A.Array [A.UnknownDimension]) $ typeOfVariable c
            A.Retypes _ _ t _ -> return t
            A.RetypesExpr _ _ t _ -> return t
            _ -> die $ "cannot type name " ++ show st

--{{{  identifying types
typeOfRecordField :: (PSM m, Die m) => A.Type -> A.Name -> m A.Type
typeOfRecordField (A.UserDataType rec) field
    =  do st <- specTypeOfName rec
          case st of
            A.DataTypeRecord _ _ fs -> checkJust "unknown record field" $ lookup field fs
            _ -> die "not record type"
typeOfRecordField _ _ = die "not record type"

subscriptType :: (PSM m, Die m) => A.Subscript -> A.Type -> m A.Type
subscriptType (A.SubscriptFromFor _ _ _) t = return t
subscriptType (A.SubscriptFrom _ _) t = return t
subscriptType (A.SubscriptFor _ _) t = return t
subscriptType (A.SubscriptField _ tag) t = typeOfRecordField t tag
subscriptType (A.Subscript _ _) (A.Array [_] t) = return t
subscriptType (A.Subscript _ _) (A.Array (_:ds) t) = return $ A.Array ds t
subscriptType _ _ = die "unsubscriptable type"

typeOfVariable :: (PSM m, Die m) => A.Variable -> m A.Type
typeOfVariable (A.Variable m n) = typeOfName n
typeOfVariable (A.SubscriptedVariable m s v)
    = typeOfVariable v >>= subscriptType s

abbrevModeOfVariable :: (PSM m, Die m) => A.Variable -> m A.AbbrevMode
abbrevModeOfVariable (A.Variable _ n) = abbrevModeOfName n
abbrevModeOfVariable (A.SubscriptedVariable _ sub v)
    =  do am <- abbrevModeOfVariable v
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

typeOfExpression :: (PSM m, Die m) => A.Expression -> m A.Type
typeOfExpression e
    = case e of
        A.Monadic m op e -> typeOfExpression e
        A.Dyadic m op e f ->
          if dyadicIsBoolean op then return A.Bool else typeOfExpression e
        A.MostPos m t -> return t
        A.MostNeg m t -> return t
        A.SizeType m t -> return A.Int
        A.SizeExpr m t -> return A.Int
        A.SizeVariable m t -> return A.Int
        A.Conversion m cm t e -> return t
        A.ExprVariable m v -> typeOfVariable v
        A.ExprLiteral m l -> typeOfLiteral l
        A.True m -> return A.Bool
        A.False m -> return A.Bool
        A.FunctionCall m n es -> liftM head $ returnTypesOfFunction n
        A.SubscriptedExpr m s e ->
          typeOfExpression e >>= subscriptType s
        A.BytesInExpr m e -> return A.Int
        A.BytesInType m t -> return A.Int
        A.OffsetOf m t n -> return A.Int

typeOfLiteral :: (PSM m, Die m) => A.Literal -> m A.Type
typeOfLiteral (A.Literal m t lr) = return t
typeOfLiteral (A.SubscriptedLiteral m s l)
    = typeOfLiteral l >>= subscriptType s
--}}}

returnTypesOfFunction :: (PSM m, Die m) => A.Name -> m [A.Type]
returnTypesOfFunction n
    =  do st <- specTypeOfName n
          case st of
            A.Function m rs fs vp -> return rs
            -- If it's not defined as a function, it might have been converted to a proc.
            _ ->
              do ps <- get
                 checkJust "not defined as a function" $
                   lookup (A.nameName n) (psFunctionReturns ps)

-- | Get the items in a channel's protocol (for typechecking).
-- Returns Left if it's a simple protocol, Right if it's tagged.
protocolItems :: (PSM m, Die m) => A.Variable -> m (Either [A.Type] [(A.Name, [A.Type])])
protocolItems v
    =  do A.Chan t <- typeOfVariable v
          case t of
            A.UserProtocol proto ->
              do st <- specTypeOfName proto
                 case st of
                   A.Protocol _ ts -> return $ Left ts
                   A.ProtocolCase _ nts -> return $ Right nts
            _ -> return $ Left [t]

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

-- | Given the abbreviation mode of something, return what the abbreviation
-- mode of something that abbreviated it would be.
makeAbbrevAM :: A.AbbrevMode -> A.AbbrevMode
makeAbbrevAM A.Original = A.Abbrev
makeAbbrevAM am = am

-- | Generate a constant expression from an integer -- for array sizes and the like.
makeConstant :: Meta -> Int -> A.Expression
makeConstant m n = A.ExprLiteral m $ A.Literal m A.Int $ A.IntLiteral m (show n)

-- | Find the Meta value in an expression.
metaOfExpression :: A.Expression -> Meta
metaOfExpression e = head $ gmapQ (mkQ emptyMeta findMeta) e
  where
    findMeta :: Meta -> Meta
    findMeta m = m

-- | Will a conversion between two types always succeed?
isSafeConversion :: A.Type -> A.Type -> Bool
isSafeConversion fromT toT = (fromP /= -1) && (toP /= -1) && (fromP <= toP)
  where
    fromP = precNum fromT
    toP = precNum toT

    precNum :: A.Type -> Int
    precNum t = precNum' t 0 convPrec

    precNum' :: A.Type -> Int -> [[A.Type]] -> Int
    precNum' _ n [] = (-1)
    precNum' t n (tl:tls)
        = if t `elem` tl then n
                         else precNum' t (n + 1) tls

    convPrec :: [[A.Type]]
    convPrec
        = [ [A.Bool]
          , [A.Byte]
          , [A.Int16]
          , [A.Int, A.Int32]
          , [A.Int64]
          ]

--{{{ classes of types
-- | Scalar integer types.
isIntegerType :: A.Type -> Bool
isIntegerType t
    = case t of
        A.Byte -> True
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
--}}}
