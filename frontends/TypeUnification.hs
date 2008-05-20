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
import Control.Monad.State
import Control.Monad.Trans
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe
import Data.IORef

import qualified AST as A
import Errors
import Metadata
import Pass
import ShowCode
import UnifyType
import Utils

foldCon :: ([A.Type] -> A.Type) -> [Either String A.Type] -> Either String A.Type
foldCon con es = case splitEither es of
  ([],ts) -> Right $ con ts
  ((e:_),_) -> Left e

-- Much of the code in this module is taken from or based on Tim Sheard's Haskell
-- listing of a simple type unification algorithm at the beginning of his
-- paper "Generic Unification via Two-Level Types and Parameterized Modules Functional
-- Pearl (2001)", citeseer: http://citeseer.ist.psu.edu/451401.html
-- This in turn was taken from Luca Cardelli's "Basic Polymorphic Type Checking"

unifyRainTypes :: forall k. (Ord k, Show k) => (Map.Map k (TypeExp A.Type)) -> [(k, k)] ->
  PassM (Map.Map k A.Type)
unifyRainTypes m' prs
  =   do mapM_ (\(x,y) -> unifyType (lookupStartType x m') (lookupStartType y m')) prs
         stToMap m'
  where
    lookupStartType :: k -> Map.Map k (TypeExp A.Type) -> TypeExp A.Type
    lookupStartType s m = case Map.lookup s m of
      Just x -> x
      Nothing -> error $ "Could not find type for variable in map before unification: "
        ++ show s

    stToMap :: Map.Map k (TypeExp A.Type) -> PassM (Map.Map k A.Type)
    stToMap m = do m' <- liftIO $ mapMapWithKeyM (\k v -> prune v >>= read k) m
                   let (mapOfErrs, mapOfRes) = Map.mapEitherWithKey (const id) m'
                   case Map.elems mapOfErrs of
                     ((m,e):_) -> dieP m e
                     [] -> return mapOfRes
      where
        read :: k -> TypeExp A.Type -> IO (Either (Meta, String) A.Type)
        read k (OperType m _ con vals)
          = do vals' <- mapM (read k) vals
               case foldCon con (map (either (Left . snd) Right) vals') of
                 Left e -> return $ Left (m, e)
                 Right x -> return $ Right x
        read k (MutVar m v) = readIORef v >>= \t -> case t of
          Nothing -> return $ Left (m, "Type error in unification, "
            ++ "ambigious type remains for: " ++ show k)
          Just t' -> read k t'
        read k (NumLit m v) = readIORef v >>= \x -> case x of
          Left _ -> return $ Left (m, "Type error in unification, "
            ++ "ambigious type remains for numeric literal: " ++ show k)
          Right t -> return $ Right t

fromTypeExp :: TypeExp A.Type -> PassM A.Type
fromTypeExp x = fromTypeExp' =<< (liftIO $ prune x)
  where
    fromTypeExp' :: TypeExp A.Type -> PassM A.Type
    fromTypeExp' (MutVar m _) = dieP m "Unresolved type"
    fromTypeExp' (GenVar m _) = dieP m "Template vars not yet supported"
    fromTypeExp' (NumLit m v) = liftIO (readIORef v) >>= \x -> case x of
      Left (n:_) -> dieP m $ "Ambigiously typed numeric literal: " ++ show n
      Right t -> return t
    fromTypeExp' (OperType _ _ f ts) = mapM fromTypeExp ts >>* f

-- For debugging:
showInErr :: TypeExp A.Type -> PassM String
showInErr (MutVar {}) = return "MutVar"
showInErr (GenVar {}) = return "GenVar"
showInErr (NumLit {}) = return "NumLit"
showInErr t@(OperType {}) = showCode =<< fromTypeExp t

giveErr :: Meta -> String -> TypeExp A.Type -> TypeExp A.Type -> PassM a
giveErr m msg tx ty
  =        do x <- showInErr tx
              y <- showInErr ty
              dieP m $ msg ++ x ++ " and " ++ y

prune :: Typeable a => TypeExp a -> IO (TypeExp a)
prune t =
 case t of
   MutVar _ r ->
     do m <- readIORef r
        case m of
          Nothing -> return t
          Just t2 ->
            do t' <- prune t2
               writeIORef r (Just t')
               return t'
   _ -> return t

occursInType :: Typeable a => Ptr a -> TypeExp a -> IO Bool
occursInType r t =
  do t' <- prune t
     case t' of
       MutVar _ r2 -> return $ r == r2
       GenVar _ n -> return False
       OperType _ _ _ ts -> mapM (occursInType r) ts >>* or

unifyType :: TypeExp A.Type -> TypeExp A.Type -> PassM ()
unifyType te1 te2
  = do t1' <- liftIO $ prune te1
       t2' <- liftIO $ prune te2
       case (t1',t2') of
         (MutVar _ r1, MutVar _ r2) ->
           if r1 == r2
             then return ()
             else liftIO $ writeIORef r1 (Just t2')
         (MutVar m r1, _) ->
           do b <- liftIO $ occursInType r1 t2'
              if b
                then dieP m "Infinitely recursive type formed"
                else liftIO $ writeIORef r1 (Just t2')
         (_,MutVar {}) -> unifyType t2' t1'
         (GenVar m x,GenVar _ y) ->
           if x == y then return () else dieP m $ "different template variables"
             ++ " cannot be assumed to be equal"
         (OperType m1 n1 _ ts1,OperType m2 n2 _ ts2) ->
           if n1 == n2
              then unifyArgs ts1 ts2
              else giveErr m1 "Type cannot be matched: " t1' t2'
         (NumLit m1 vns1, NumLit m2 vns2) ->
           do nst1 <- liftIO $ readIORef vns1
              nst2 <- liftIO $ readIORef vns2
              case (nst1, nst2) of
                (Right t1, Right t2) ->
                  if t1 /= t2
                    then dieP m1 "Numeric literals bound to different types"
                    else return ()
                (Left ns1, Left ns2) ->
                  do liftIO $ writeIORef vns1 $ Left (ns1 ++ ns2)
                     liftIO $ writeIORef vns2 $ Left (ns2 ++ ns1)
                (Right {}, Left {}) -> unifyType t2' t1'
                (Left ns1, Right t2) ->
                  if all (willFit t2) (map snd ns1)
                    then liftIO $ writeIORef vns1 (Right t2)
                    else dieP m1 "Numeric literals will not fit in concrete type"
         (OperType {}, NumLit {}) -> unifyType t2' t1'
         (NumLit m1 vns1, OperType m2 n2 f ts2) ->
           do nst1 <- liftIO $ readIORef vns1
              case nst1 of
                Right t ->
                  if null ts2 && t == f []
                    then return ()
                    else dieP m1 $ "numeric literal cannot be unified"
                           ++ " with two different types"
                Left ns ->
                  if null ts2
                    then if all (willFit $ f []) (map snd ns)
                           then liftIO $  writeIORef vns1 $ Right (f [])
                           else dieP m1 "Numeric literals will not fit in concrete type"
                    else dieP m1 $  "Numeric literal cannot be unified"
                      ++ " with non-numeric type"
         (t,_) -> dieP (findMeta t) "different types"
  where
    unifyArgs (x:xs) (y:ys) = unifyType x y >> unifyArgs xs ys
    unifyArgs [] [] = return ()
    unifyArgs xs ys = dieP (findMeta (xs,ys)) "different lengths"

instantiate :: Typeable a => [TypeExp a] -> TypeExp a -> TypeExp a
instantiate ts x = case x of
  MutVar _ _ -> x
  OperType m nm f xs -> OperType m nm f (map (instantiate ts) xs)
  GenVar _ n -> ts !! n

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

