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

-- | Traversal strategies over the AST and other data types.
module Traversal (
    ExplicitTrans, Transform, Check
  , transformToExplicitDepth, checkToTransform
  , applyExplicitM, applyExplicitM2, applyExplicitM9
  , applyDepthM, applyDepthM2
  , checkDepthM
  ) where

import Data.Generics

import GenericUtils
import Pass

-- | A transformation for a single 'Data' type with explicit descent.
-- The first argument passed is a function that can be called to explicitly
-- descend into a generic value.
type ExplicitTrans t = (forall s. Data s => s -> PassM s) -> t -> PassM t

-- | A transformation for a single 'Data' type with implicit descent.
-- This can be applied recursively throughout a data structure.
type Transform t = t -> PassM t

-- | A check for a single 'Data' type with implicit descent.
-- This is like 'Transform', but it doesn't change the value; it may fail or
-- modify the state, though.
type Check t = t -> PassM ()

-- | Make an 'ExplicitTrans' that applies a 'Transform', recursing depth-first.
transformToExplicitDepth :: Data t => Transform t -> ExplicitTrans t
transformToExplicitDepth f descend x = descend x >>= f

-- | Make a 'Transform' that applies a 'Check'.
checkToTransform :: Data t => Check t -> Transform t
checkToTransform f x = f x >> return x

-- | Apply an explicit transformation.
applyExplicitM :: forall t1 s. (Data t1, Data s) =>
                  ExplicitTrans t1 -> s -> PassM s
applyExplicitM f1 = doGeneric `extM` (doSpecific f1)
  where
    typeSet :: [TypeKey]
    typeSet = [typeKey (undefined :: t1)]

    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapMFor typeSet (applyExplicitM f1)

    doSpecific :: Data t => ExplicitTrans t -> t -> PassM t
    doSpecific f x = f doGeneric x

-- | Apply two explicit transformations.
applyExplicitM2 :: forall t1 t2 s. (Data t1, Data t2, Data s) =>
                   ExplicitTrans t1 -> ExplicitTrans t2 -> s -> PassM s
applyExplicitM2 f1 f2 = doGeneric `extM` (doSpecific f1)
                                  `extM` (doSpecific f2)
  where
    typeSet :: [TypeKey]
    typeSet = [ typeKey (undefined :: t1)
              , typeKey (undefined :: t2)
              ]

    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapMFor typeSet (applyExplicitM2 f1 f2)

    doSpecific :: Data t => ExplicitTrans t -> t -> PassM t
    doSpecific f x = f doGeneric x

-- | Apply nine explicit transformations (!).
applyExplicitM9 :: forall t1 t2 t3 t4 t5 t6 t7 t8 t9 s.
                   (Data t1, Data t2, Data t3, Data t4, Data t5, Data t6,
                    Data t7, Data t8, Data t9, Data s) =>
                   ExplicitTrans t1
                   -> ExplicitTrans t2
                   -> ExplicitTrans t3
                   -> ExplicitTrans t4
                   -> ExplicitTrans t5
                   -> ExplicitTrans t6
                   -> ExplicitTrans t7
                   -> ExplicitTrans t8
                   -> ExplicitTrans t9
                   -> s -> PassM s
applyExplicitM9 f1 f2 f3 f4 f5 f6 f7 f8 f9
    = doGeneric `extM` (doSpecific f1)
                `extM` (doSpecific f2)
                `extM` (doSpecific f3)
                `extM` (doSpecific f4)
                `extM` (doSpecific f5)
                `extM` (doSpecific f6)
                `extM` (doSpecific f7)
                `extM` (doSpecific f8)
                `extM` (doSpecific f9)
  where
    typeSet :: [TypeKey]
    typeSet = [ typeKey (undefined :: t1)
              , typeKey (undefined :: t2)
              , typeKey (undefined :: t3)
              , typeKey (undefined :: t4)
              , typeKey (undefined :: t5)
              , typeKey (undefined :: t6)
              , typeKey (undefined :: t7)
              , typeKey (undefined :: t8)
              , typeKey (undefined :: t9)
              ]

    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapMFor typeSet (applyExplicitM9 f1 f2 f3 f4 f5 f6 f7 f8 f9)

    doSpecific :: Data t => ExplicitTrans t -> t -> PassM t
    doSpecific f x = f doGeneric x

-- | Apply a transformation, recursing depth-first.
applyDepthM :: forall t1 s. (Data t1, Data s) =>
               Transform t1 -> s -> PassM s
applyDepthM f = applyExplicitM (transformToExplicitDepth f)

-- | Apply two transformations, recursing depth-first.
applyDepthM2 :: forall t1 t2 s. (Data t1, Data t2, Data s) =>
                Transform t1 -> Transform t2 -> s -> PassM s
applyDepthM2 f1 f2 = applyExplicitM2 (transformToExplicitDepth f1)
                                     (transformToExplicitDepth f2)

-- | Apply a check, recursing depth-first.
checkDepthM :: forall t1 s. (Data t1, Data s) =>
               Check t1 -> s -> PassM s
checkDepthM f = applyDepthM (checkToTransform f)

