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

-- | Evaluate simple literal expressions.
module EvalLiterals where

import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.State
import Data.Char
import Data.Generics
import Data.Int
import Data.Maybe
import Data.Word
import Numeric

import qualified AST as A
import CompState hiding (CSM) -- everything here is read-only
import Errors
import Metadata
import Traversal
import TypeSizes

type EvalM = ErrorT ErrorReport (StateT CompState Identity)

instance Die EvalM where
  dieReport = throwError

-- | Evaluated values of various types.
data OccValue =
  OccBool Bool
  | OccByte Word8
  | OccUInt16 Word16
  | OccUInt32 Word32
  | OccUInt64 Word64
  | OccInt8 Int8
  | OccInt16 Int16
  | OccInt CIntReplacement
  | OccInt32 Int32
  | OccInt64 Int64
  | OccReal32 Float
  | OccReal64 Double
  | OccArray [OccValue]
  | OccRecord A.Name [OccValue]
  deriving (Show, Eq, Typeable, Data)

-- | Is an expression a constant literal?
isConstant :: A.Expression -> Bool
isConstant (A.Literal _ _ (A.ArrayListLiteral _ aes))
    = isConstantStruct aes
isConstant (A.Literal _ _ (A.RecordLiteral _ es))
    = and $ map isConstant es
isConstant (A.Literal _ _ _) = True
isConstant (A.True _) = True
isConstant (A.False _) = True
isConstant _ = False

-- | Is an array literal element constant?
isConstantStruct :: A.Structured A.Expression -> Bool
isConstantStruct (A.Several _ ss) = and $ map isConstantStruct ss
isConstantStruct (A.Only _ e) = isConstant e
isConstantStruct (A.ProcThen {}) = False
isConstantStruct (A.Spec {}) = False

-- | Evaluate a byte literal.
evalByte :: (CSMR m, Die m) => Meta -> String -> m Char
evalByte m s
    =  do ps <- getCompState
          case runEvaluator ps (evalByteLiteral m OccByte s) of
            Left (m', err) ->
              dieReport (m', "Cannot evaluate byte literal: " ++ err)
            Right (OccByte ch) ->
              return (chr $ fromIntegral ch)

-- | Run an evaluator operation.
runEvaluator :: CompState -> EvalM OccValue -> Either ErrorReport OccValue
runEvaluator ps func
    = runIdentity (evalStateT (runErrorT func) ps)

-- | Evaluate a simple literal expression.
evalSimpleExpression :: A.Expression -> EvalM OccValue
evalSimpleExpression e@(A.Literal _ _ _) = evalSimpleLiteral e
evalSimpleExpression e = throwError (Just $ findMeta e, "Not a literal")

-- | Turn the result of one of the read* functions into an OccValue,
-- or throw an error if it didn't parse.
fromRead :: Meta -> (a -> OccValue) -> (String -> [(a, String)])
            -> String -> EvalM OccValue
fromRead m cons reader s
    = case reader s of
        [(v, "")] -> return $ cons v
        _ -> throwError (Just m, "Cannot parse literal: " ++ s)

-- | Evaluate a simple (non-array) literal.
evalSimpleLiteral :: A.Expression -> EvalM OccValue
evalSimpleLiteral (A.Literal m t lr)
    = underlyingType m t >>= \t' -> case t' of
        A.Infer  -> defaults
        A.Byte   -> into OccByte
        A.UInt16 -> into OccUInt16
        A.UInt32 -> into OccUInt32
        A.UInt64 -> into OccUInt64
        A.Int8   -> into OccInt8
        A.Int16  -> into OccInt16
        A.Int    -> into OccInt
        A.Int32  -> into OccInt32
        A.Int64  -> into OccInt64
        A.Real32 -> intoF OccReal32
        A.Real64 -> intoF OccReal64
        _        -> bad
  where
    defaults :: EvalM OccValue
    defaults
        = case lr of
            A.ByteLiteral _ s -> evalByteLiteral m OccByte s
            A.IntLiteral _ s  -> fromRead m OccInt (readSigned readDec) s
            A.HexLiteral _ s  -> fromRead m OccInt readHex s
            A.RealLiteral _ s -> fromRead m OccReal32 readFloat' s
            _                 -> bad

    into :: (Num t, Real t) => (t -> OccValue) -> EvalM OccValue
    into cons
        = case lr of
            A.ByteLiteral _ s -> evalByteLiteral m cons s
            A.IntLiteral _ s  -> fromRead m cons (readSigned readDec) s
            A.HexLiteral _ s  -> fromRead m cons readHex s
            _                 -> bad

    intoF :: RealFrac t => (t -> OccValue) -> EvalM OccValue
    intoF cons
        = case lr of
            A.ByteLiteral _ s -> evalByteLiteral m cons s
            A.IntLiteral _ s  -> fromRead m cons (readSigned readDec) s
            A.HexLiteral _ s  -> fromRead m cons readHex s
            A.RealLiteral _ s -> fromRead m cons readFloat' s
            _                 -> bad

    -- readFloat only handles unsigned values, so we need to look out for the negation
    -- ourselves:
    readFloat' :: RealFrac a => ReadS a
    readFloat' [] = []
    readFloat' ('-':rest) = [(negate x, s) | (x, s) <- readFloat rest]
    readFloat' s = readFloat s


    bad :: EvalM OccValue
    bad = throwError (Just m, "Cannot evaluate literal")

    m = findMeta lr

-- | Evaluate a byte literal.
evalByteLiteral :: Num t => Meta -> (t -> OccValue) -> String -> EvalM OccValue
evalByteLiteral m cons ('*':'#':hex)
    = do OccInt n <- fromRead m OccInt readHex hex
         return $ cons (fromIntegral n)
evalByteLiteral _ cons ['*', ch]
    = return $ cons (fromIntegral $ ord $ star ch)
  where
    star :: Char -> Char
    star 'c' = '\r'
    star 'n' = '\n'
    star 't' = '\t'
    star 's' = ' '
    star c = c
evalByteLiteral _ cons [ch]
    = return $ cons (fromIntegral $ ord ch)
evalByteLiteral m _ _ = throwError (Just m, "Bad BYTE literal")

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
