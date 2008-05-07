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
  , baseX, extX, extD, extC, applyX
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

-- | A set of generic transformations.
type InfoX = ([TypeKey],
              (forall dgt. Data dgt => dgt -> PassM dgt)
              -> (forall t1. Data t1 => t1 -> PassM t1)
              -> (forall t2. Data t2 => t2 -> PassM t2))

-- | An empty set of transformations.
baseX :: InfoX
baseX = ([], (\doGeneric t -> t))

-- | Add an 'ExplicitTrans' to a set.
extX :: forall t. Data t => InfoX -> ExplicitTrans t -> InfoX
extX (tks, g) f = ((typeKey (undefined :: t)) : tks,
                   (\doGeneric t -> (g doGeneric t) `extM` (f doGeneric)))

-- | Add a 'Transform' to a set, to be applied depth-first.
extD :: forall t. Data t => InfoX -> Transform t -> InfoX
extD info f = extX info (transformToExplicitDepth f)

-- | Add a 'Check' to a set, to be applied depth-first.
extC :: forall t. Data t => InfoX -> Check t -> InfoX
extC info f = extD info (checkToTransform f)

-- | Apply a set of transformations.
applyX :: Data s => InfoX -> s -> PassM s
applyX info@(tks, maker) = trans
  where
    ts :: TypeSet
    ts = makeTypeSet tks

    trans :: Data s => s -> PassM s
    trans = maker doGeneric doGeneric

    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapMFor ts trans

-- | Apply a transformation, recursing depth-first.
applyDepthM :: forall t1 s. (Data t1, Data s) =>
               Transform t1 -> s -> PassM s
applyDepthM f1
    = applyX $ baseX `extD` f1

-- | Apply two transformations, recursing depth-first.
applyDepthM2 :: forall t1 t2 s. (Data t1, Data t2, Data s) =>
                Transform t1 -> Transform t2 -> s -> PassM s
applyDepthM2 f1 f2
    = applyX $ baseX `extD` f1 `extD` f2

-- | Apply a check, recursing depth-first.
checkDepthM :: forall t1 s. (Data t1, Data s) =>
               Check t1 -> s -> PassM s
checkDepthM f1
    = applyX $ baseX `extC` f1

