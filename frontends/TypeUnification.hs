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

import Control.Monad.ST
import Data.Generics
import qualified Data.Map as Map
import Data.STRef

import qualified AST as A
import Utils

-- Much of the code in this module is taken from or based on Tim Sheard's Haskell
-- listing of a simple type unification algorithm at the beginning of his
-- paper "Generic Unification via Two-Level Types and Parameterized Modules Functional
-- Pearl (2001)", citeseer: http://citeseer.ist.psu.edu/451401.html
-- This in turn was taken from Luca Cardelli's "Basic Polymorphic Type Checking"

unifyRainTypes :: Map.Map String A.Type -> [(String, String)] -> Map.Map String A.Type
unifyRainTypes m prs
  = runST $ do m' <- mapToST m
               mapM_ (\(x,y) -> unifyType (lookupStartType x m') (lookupStartType y
                 m')) prs
               stToMap m'
  where
    lookupStartType :: String -> Map.Map String (TypeExp s A.Type) -> TypeExp
      s A.Type
    lookupStartType s m = case Map.lookup s m of
      Just x -> x
      Nothing -> error $ "Could not find type for variable in map before unification: "
        ++ s

    mapToST :: Map.Map String A.Type -> ST s (Map.Map String (TypeExp s A.Type))
    mapToST = mapMapM typeToTypeExp

    stToMap :: Map.Map String (TypeExp s A.Type) -> ST s (Map.Map String
      A.Type)
    stToMap = mapMapM (read <.< prune)
      where
        read :: TypeExp s A.Type -> ST s A.Type
        read (OperType con vals) = do vals' <- mapM read vals
                                      return $ fromConstr con -- vals'
        read x = error $ "Type error in unification, found: " ++ show x

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
typeToTypeExp t = return $ OperType (toConstr t) []

type Ptr s a = STRef s (Maybe (TypeExp s a))

-- TODO add a special type for numeric literals
data TypeExp s a
 = MutVar (Ptr s a)
 | GenVar Int
 | OperType Constr [ TypeExp s a ]

-- For debugging:
instance Show (TypeExp s a) where
  show (MutVar {}) = "MutVar"
  show (GenVar {}) = "GenVar"
  show (OperType {}) = "OperType"

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

unifyType :: TypeExp s a -> TypeExp s a -> ST s ()
unifyType t1 t2
  = do t1' <- prune t1
       t2' <- prune t2
       case (t1',t2') of
         (MutVar r1, MutVar r2) ->
           if r1 == r2
             then return ()
             else writeSTRef r1 (Just t2')
         (MutVar r1, _) ->
           do b <- occursInType r1 t2'
              if b
                then error "occurs in"
                else writeSTRef r1 (Just t2')
         (_,MutVar _) -> unifyType t2' t1'
         (GenVar n,GenVar m) ->
           if n == m then return () else error "different genvars"
         (OperType n1 ts1,OperType n2 ts2) ->
           if n1 == n2
              then unifyArgs ts1 ts2
              else error "different constructors"
         (_,_) -> error "different types"
  where
    unifyArgs (x:xs) (y:ys) = do unifyType x y
                                 unifyArgs xs ys
    unifyArgs [] [] = return ()
    unifyArgs _ _ = error "different lengths"

instantiate :: [TypeExp s a] -> TypeExp s a -> TypeExp s a
instantiate ts x = case x of
  MutVar _ -> x
  OperType nm xs -> OperType nm (map (instantiate ts) xs)
  GenVar n -> ts !! n

