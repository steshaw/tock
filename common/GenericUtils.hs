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

-- | Utilities for generic operations.
--
-- This code was inspired by Neil Mitchell's Uniplate library.
-- 'typeContains' is faster than PlateData's equivalent at the cost of some
-- flexibility: it'll only work for types that it knows about (which can be
-- added to in the definition of 'contains').
module GenericUtils (typeContains, gmapMFor, gmapMFor2) where

import Data.Generics
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List
import Data.Typeable
import System.IO.Unsafe

import qualified AST as A

data DataBox = forall a. (Typeable a, Data a) => DataBox a

-- | Given a witness for a type, return witnesses for all the types that its
-- constructors take.
constrArgTypes :: (Data a, Typeable a) => a -> [DataBox]
constrArgTypes x = if isAlgType dtype then concatMap f constrs else []
  where
    f constr = gmapQ DataBox (asTypeOf (fromConstr constr) x)
    constrs = dataTypeConstrs dtype
    dtype = dataTypeOf x

-- | Given a witness for a type, return its type key.
typeKey :: Typeable a => a -> Int
typeKey x = unsafePerformIO $ typeRepKey $ typeOf x

-- | Given a witness for a type, return a map from type keys to witnesses for
-- all the types it contains recursively.
containsTypes :: (Data a, Typeable a) => a -> IntMap DataBox
containsTypes start = containsTypes' (DataBox start) IntMap.empty
  where
    containsTypes' :: DataBox -> IntMap DataBox -> IntMap DataBox
    containsTypes' box@(DataBox thisType) seen
        = if thisKey `IntMap.member` seen
            then seen
            else foldl (\s t -> containsTypes' t s)
                       (IntMap.insert thisKey box seen)
                       (constrArgTypes thisType)
      where
        thisKey = typeKey thisType

-- | A map from type keys to the other type keys reachable from them.
type ContainsMap = IntMap IntSet

-- | A map of reachable types.
-- At the moment this only knows about types reachable from the AST.
contains :: ContainsMap
contains = IntMap.fromList [(typeKey t,
                             IntSet.fromList $ IntMap.keys $ containsTypes t)
                            | DataBox t <- IntMap.elems allTypes]
  where
    allTypes = containsTypes (undefined :: A.AST)

-- | Does one type contain another?
-- (A type always contains itself.)
typeContains :: (Data a, Typeable a, Data b, Typeable b) => a -> b -> Bool
typeContains start find
    = if startKey == findKey
        then True
        else case IntMap.lookup startKey contains of
               Just set -> findKey `IntSet.member` set
               Nothing -> True  -- can't tell, so it might be
  where
    startKey = typeKey start
    findKey = typeKey find

-- | Type-smart generic mapM.
-- This is like 'gmapM', but it only applies the function to arguments that
-- could contain the target type.
gmapMFor :: (Monad m, Data t, Data a) =>
            a                                 -- ^ Witness for target type
            -> (forall s. Data s => s -> m s) -- ^ Function to apply
            -> (t -> m t)                     -- ^ Generic operation
gmapMFor find top = gmapM (each find top)
  where
    each :: (Monad m, Data t, Data a) =>
            a -> (forall s. Data s => s -> m s) -> (t -> m t)
    each find top x
        = if cont then top x else return x
      where cont = x `typeContains` find

-- | Two-type version of 'gmapMFor'.
gmapMFor2 :: (Monad m, Data t, Data a1, Data a2) =>
             a1                                -- ^ Witness for target type 1
             -> a2                             -- ^ Witness for target type 2
             -> (forall s. Data s => s -> m s) -- ^ Function to apply
             -> (t -> m t)                     -- ^ Generic operation
gmapMFor2 find1 find2 top = gmapM (each find1 find2 top)
  where
    each :: (Monad m, Data t, Data a1, Data a2) =>
            a1 -> a2 -> (forall s. Data s => s -> m s) -> (t -> m t)
    each find1 find2 top x
        = if cont then top x else return x
      where cont = x `typeContains` find1 || x `typeContains` find2

