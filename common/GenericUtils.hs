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
module GenericUtils (
    TypeKey, typeKey
  , containsTypes
  , gmapMFor
  ) where

import Data.Generics
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List
import Data.Typeable
import System.IO.Unsafe

import qualified AST as A

-- | A type identifier.
type TypeKey = Int

-- | Given a witness for a type, return its 'TypeKey'.
typeKey :: Typeable a => a -> TypeKey
typeKey x = unsafePerformIO $ typeRepKey $ typeOf x

-- | Container for 'Data' items.
data DataBox = forall a. (Typeable a, Data a) => DataBox a

-- | Given a witness for a type, return witnesses for all the types that its
-- constructors take.
constrArgTypes :: (Data a, Typeable a) => a -> [DataBox]
constrArgTypes x = if isAlgType dtype then concatMap f constrs else []
  where
    f constr = gmapQ DataBox (asTypeOf (fromConstr constr) x)
    constrs = dataTypeConstrs dtype
    dtype = dataTypeOf x

-- | Given a witness for a type, return a map from type keys to witnesses for
-- all the types it contains recursively.
containedTypes :: (Data a, Typeable a) => a -> IntMap DataBox
containedTypes start = containedTypes' (DataBox start) IntMap.empty
  where
    containedTypes' :: DataBox -> IntMap DataBox -> IntMap DataBox
    containedTypes' box@(DataBox thisType) seen
        = if thisKey `IntMap.member` seen
            then seen
            else foldl (\s t -> containedTypes' t s)
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
                             IntMap.keysSet $ containedTypes t)
                            | DataBox t <- IntMap.elems allTypes]
  where
    allTypes = containedTypes (undefined :: A.AST)

-- | Does a value contain any of the listed types?
-- (A value always contains its own type.)
containsTypes :: Data t => t -> [TypeKey] -> Bool
containsTypes x targets
    = or $ map containsType targets
  where
    start :: TypeKey
    start = typeKey x

    containsType :: TypeKey -> Bool
    containsType target
      | start == target = True
      | otherwise       = case IntMap.lookup start contains of
                            Just set -> target `IntSet.member` set
                            Nothing -> True  -- can't tell, so it might be

-- | Type-smart generic mapM.
-- This is like 'gmapM', but it only applies the function to arguments that
-- could contain any of the target types.
gmapMFor :: (Monad m, Data t) =>
            [TypeKey]                         -- ^ Target types
            -> (forall s. Data s => s -> m s) -- ^ Function to apply
            -> (t -> m t)                     -- ^ Generic operation
gmapMFor targets f = gmapM (each f)
  where
    each :: (Monad m, Data t) =>
            (forall s. Data s => s -> m s) -> (t -> m t)
    each f x
        = if containsTypes x targets then f x else return x
