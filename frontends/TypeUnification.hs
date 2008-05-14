{-
Tock: a compiler for parallel languages
Copyright (C) 2008  University of Kent

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

module TypeUnification where

import Control.Monad
import Control.Monad.ST
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe
import Data.STRef

import qualified AST as A
import Utils

foldCon :: Constr -> [Either String A.Type] -> Either String A.Type
foldCon con [] = Right $ fromConstr con
foldCon con [Left e] = Left e
foldCon con [Right t] = Right $ fromConstrB (fromJust $ cast t) con
foldCon con _ = Left "foldCon: too many arguments given"


-- Much of the code in this module is taken from or based on Tim Sheard's Haskell
-- listing of a simple type unification algorithm at the beginning of his
-- paper "Generic Unification via Two-Level Types and Parameterized Modules Functional
-- Pearl (2001)", citeseer: http://citeseer.ist.psu.edu/451401.html
-- This in turn was taken from Luca Cardelli's "Basic Polymorphic Type Checking"

unifyRainTypes :: forall k. (Ord k, Show k) => Map.Map k A.Type -> [(k, k)] -> Either String
  (Map.Map k A.Type)
unifyRainTypes m prs
  = runST $ do m' <- mapToST m
               outs <- mapM (\(x,y) -> unifyType (lookupStartType x m') (lookupStartType y
                 m')) prs
               case mapMaybe (either Just (const Nothing)) outs of
                 (err:_) -> return $ Left err
                 [] -> stToMap m'
  where
    lookupStartType :: k -> Map.Map k (TypeExp s A.Type) -> TypeExp
      s A.Type
    lookupStartType s m = case Map.lookup s m of
      Just x -> x
      Nothing -> error $ "Could not find type for variable in map before unification: "
        ++ show s

    mapToST :: Map.Map k A.Type -> ST s (Map.Map k (TypeExp s A.Type))
    mapToST = mapMapM typeToTypeExp

    stToMap :: Map.Map k (TypeExp s A.Type) -> ST s (Either String (Map.Map k A.Type))
    stToMap m = do m' <- mapMapM (read <.< prune) m
                   let (mapOfErrs, mapOfRes) = Map.mapEitherWithKey (const id) m'
                   case Map.elems mapOfErrs of
                     (e:_) -> return $ Left e
                     [] -> return $ Right mapOfRes
      where
        read :: TypeExp s A.Type -> ST s (Either String A.Type)
        read (OperType con vals) = do vals' <- mapM read vals
                                      return $ foldCon con vals'
        read (MutVar v) = readSTRef v >>= \t -> case t of
          Nothing -> return $ Left $ "Type error in unification, found non-unified type"
          Just t' -> read t'
        read (NumLit v) = readSTRef v >>= \x -> case x of
          Left _ -> return $ Left $ "Numeric type without concrete type"
          Right t -> return $ Right t
        read x = return $ Left $ "Type error in unification, found: " ++ show x
                  ++ " in: " ++ show m

ttte :: Data b => b -> A.Type -> ST s (TypeExp s A.Type)
ttte c t = typeToTypeExp t >>= \t' -> return $ OperType (toConstr c) [t']

-- Transforms the given type into a typeexp, such that the only inner types
-- left will be the primitive types (integer types, float types, bool, time).  Arrays
-- (which would require unification of dimensions and such) are not supported,
-- neither are records.
--  User data types should not be present in the input.
typeToTypeExp :: A.Type -> ST s (TypeExp s A.Type)
typeToTypeExp x@(A.List t) = ttte x t
typeToTypeExp (A.Chan A.DirInput _ t) = ttte "?" t
typeToTypeExp (A.Chan A.DirOutput _ t) = ttte "!" t
typeToTypeExp (A.Chan A.DirUnknown _ t) = ttte "channel" t
typeToTypeExp (A.Mobile t) = ttte "MOBILE" t
typeToTypeExp (A.Infer) = do r <- newSTRef Nothing
                             return $ MutVar r
typeToTypeExp (A.InferNum n) = do r <- newSTRef $ Left [n]
                                  return $ NumLit r
typeToTypeExp t = return $ OperType (toConstr t) []

type Ptr s a = STRef s (Maybe (TypeExp s a))

data TypeExp s a
 = MutVar (Ptr s a)
 | GenVar Int
 -- Either a list of integers that must fit, or a concrete type
 | NumLit (STRef s (Either [Integer] A.Type))
 | OperType Constr [ TypeExp s a ]

-- For debugging:
instance Show (TypeExp s a) where
  show (MutVar {}) = "MutVar"
  show (GenVar {}) = "GenVar"
  show (NumLit {}) = "NumLit"
  show (OperType _ ts) = "OperType " ++ show ts

prune :: TypeExp s a -> ST s (TypeExp s a)
prune t =
 case t of
   MutVar r ->
     do m <- readSTRef r
        case m of
          Nothing -> return t
          Just t2 ->
            do t' <- prune t2
               writeSTRef r (Just t')
               return t'
   _ -> return t

occursInType :: Ptr s a -> TypeExp s a -> ST s Bool
occursInType r t =
  do t' <- prune t
     case t' of
       MutVar r2 -> return $ r == r2
       GenVar n -> return False
       OperType nm ts ->
             do bs <- mapM (occursInType r) ts
                return (or bs)

unifyType :: TypeExp s a -> TypeExp s a -> ST s (Either String ())
unifyType te1 te2
  = do t1' <- prune te1
       t2' <- prune te2
       case (t1',t2') of
         (MutVar r1, MutVar r2) ->
           if r1 == r2
             then return $ Right ()
             else liftM Right $ writeSTRef r1 (Just t2')
         (MutVar r1, _) ->
           do b <- occursInType r1 t2'
              if b
                then return $ Left "occurs in"
                else liftM Right $ writeSTRef r1 (Just t2')
         (_,MutVar _) -> unifyType t2' t1'
         (GenVar n,GenVar m) ->
           if n == m then return $ Right () else return $ Left "different genvars"
         (OperType n1 ts1,OperType n2 ts2) ->
           if n1 == n2
              then unifyArgs ts1 ts2
              else return $ Left "different constructors"
         (NumLit vns1, NumLit vns2) ->
           do nst1 <- readSTRef vns1
              nst2 <- readSTRef vns2
              case (nst1, nst2) of
                (Right t1, Right t2) ->
                  if t1 /= t2
                    then return $ Left "Numeric literals bound to different types"
                    else return $ Right ()
                (Left ns1, Left ns2) ->
                  do writeSTRef vns1 $ Left (ns1 ++ ns2)
                     writeSTRef vns2 $ Left (ns1 ++ ns2)
                     return $ Right ()
                (Right {}, Left {}) -> unifyType t2' t1'
                (Left ns1, Right t2) ->
                  if all (willFit t2) ns1
                    then do writeSTRef vns1 (Right t2)
                            return $ Right ()
                    else return $ Left "Numeric literals will not fit in concrete type"
         (OperType {}, NumLit {}) -> unifyType t2' t1'
         (NumLit vns1, OperType n1 ts2) ->
           do nst1 <- readSTRef vns1
              case nst1 of
                Right t ->
                  if null ts2 && t == fromConstr n1
                    then return $ Right ()
                    else return $ Left $ "numeric literal cannot be unified"
                           ++ " with two different types"
                Left ns ->
                  if null ts2
                    then if all (willFit $ fromConstr n1) ns
                           then do writeSTRef vns1 $ Right (fromConstr n1)
                                   return $ Right ()
                           else return $ Left "Numeric literals will not fit in concrete type"
                    else return $ Left $ "Numeric literal cannot be unified"
                      ++ " with non-numeric type"
         (_,_) -> return $ Left "different types"
  where
    unifyArgs (x:xs) (y:ys) = do unifyType x y
                                 unifyArgs xs ys
    unifyArgs [] [] = return $ Right ()
    unifyArgs _ _ = return $ Left "different lengths"

instantiate :: [TypeExp s a] -> TypeExp s a -> TypeExp s a
instantiate ts x = case x of
  MutVar _ -> x
  OperType nm xs -> OperType nm (map (instantiate ts) xs)
  GenVar n -> ts !! n

willFit :: A.Type -> Integer -> Bool
willFit t n = case bounds t of
  Just (l,h) -> l <= n && n <= h
  _ -> False
  where
    unsigned, signed :: Int -> Maybe (Integer, Integer)
    signed n = Just (negate $ 2 ^ (n - 1), (2 ^ (n - 1)) - 1)
    unsigned n = Just (0, (2 ^ n) - 1)

    bounds :: A.Type -> Maybe (Integer, Integer)
    bounds A.Int8 = signed 8
    bounds A.Int16 = signed 16
    bounds A.Int32 = signed 32
    bounds A.Int64 = signed 64
    bounds A.Byte = unsigned 8
    bounds A.UInt16 = unsigned 16
    bounds A.UInt32 = unsigned 32
    bounds A.UInt64 = unsigned 64
    bounds _ = Nothing

