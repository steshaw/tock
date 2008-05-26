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
    OpsM, Ops
  , TransformM, Transform
  , CheckM, Check
  , baseOp, extOp, extOpS
  , makeDepth, extOpD, extOpSD
  , makeCheck, extOpC
  , RecurseM, Recurse, makeRecurse
  , DescendM, Descend, makeDescend
  , applyDepthM, applyDepthSM, applyDepthM2
  , checkDepthM, checkDepthM2
  ) where

import Data.Generics

import qualified AST as A
import GenericUtils
import Pass

-- | A set of generic operations.
type OpsM m = ([TypeKey], DescendM m -> RecurseM m)

-- | As 'OpsM', but specialised for 'PassM'.
type Ops = OpsM PassM

-- | A transformation for a single 'Data' type.
type TransformM m t = t -> m t

-- | As 'TransformM', but specialised for 'PassM'.
type Transform t = TransformM PassM t

-- | A check for a single 'Data' type.
-- This is like 'Transform', but it doesn't change the value; it may fail or
-- modify the state, though.
type CheckM m t = t -> m ()

-- | As 'CheckM', but specialised for 'PassM'.
type Check t = CheckM PassM t

-- | An empty set of operations.
baseOp :: forall m. Monad m => OpsM m
baseOp = ([], id)

-- | Add a 'TransformM' to a set, to be applied with explicit descent
-- (that is, the transform will be responsible for recursing into child
-- elements itself).
extOp :: forall m t. (Monad m, Data t) => OpsM m -> TransformM m t -> OpsM m
extOp (tks, g) f = ((typeKey (undefined :: t)) : tks,
                    (\descend -> g descend `extM` f))

-- | As 'extOp', but for transformations that work on all 'A.Structured' types.
extOpS :: forall m. Monad m =>
          OpsM m
          -> (forall t. Data t => TransformM m (A.Structured t))
          -> OpsM m
extOpS ops f
    = ops
      `extOp` (f :: TransformM m (A.Structured A.Variant))
      `extOp` (f :: TransformM m (A.Structured A.Process))
      `extOp` (f :: TransformM m (A.Structured A.Option))
      `extOp` (f :: TransformM m (A.Structured A.ExpressionList))
      `extOp` (f :: TransformM m (A.Structured A.Choice))
      `extOp` (f :: TransformM m (A.Structured A.Alternative))
      `extOp` (f :: TransformM m (A.Structured ()))

-- | Generate an operation that applies a 'TransformM' with automatic
-- depth-first descent.
makeDepth :: forall m t. (Monad m, Data t) =>
             OpsM m -> TransformM m t -> TransformM m t
makeDepth ops f v = descend v >>= f
  where
    descend :: DescendM m
    descend = makeDescend ops

-- | Add a 'TransformM' to a set, to be applied with automatic depth-first
-- descent.
extOpD :: forall m t. (Monad m, Data t) => OpsM m -> OpsM m -> TransformM m t -> OpsM m
extOpD ops ops0 f = ops `extOp` (makeDepth ops0 f)

-- | As 'extOpD', but for transformations that work on all 'A.Structured' types.
extOpSD :: forall m. Monad m =>
           OpsM m
           -> OpsM m
           -> (forall t. Data t => TransformM m (A.Structured t))
           -> OpsM m
extOpSD ops ops0 f = ops `extOpS` (makeDepth ops0 f)

-- | Generate an operation that applies a 'CheckM' with automatic
-- depth-first descent.
makeCheck :: forall m t. (Monad m, Data t) =>
             OpsM m -> CheckM m t -> TransformM m t
makeCheck ops f v = descend v >> f v >> return v
  where
    descend :: DescendM m
    descend = makeDescend ops

-- | Add a 'CheckM' to a set, to be applied with automatic depth-first descent.
extOpC :: forall m t. (Monad m, Data t) => OpsM m -> OpsM m -> CheckM m t -> OpsM m
extOpC ops ops0 f = ops `extOp` (makeCheck ops0 f)

-- | A function that applies a generic operation.
-- This applies the operations in the set to the provided value.
--
-- This is the type of function that you want to use to apply a generic
-- operation; a pass in Tock is usually the application of a 'RecurseM' to the
-- AST. It's also what you should use when you're writing a pass that uses
-- explicit descent, and you want to explicitly recurse into one of the
-- children of a value that one of your transformations has been applied to.
type RecurseM m = (forall t. Data t => t -> m t)

-- | As 'RecurseM', but specialised for 'PassM'.
type Recurse = RecurseM PassM

-- | Build a 'RecurseM' function from a set of operations.
makeRecurse :: forall m. Monad m => OpsM m -> RecurseM m
makeRecurse ops@(_, f) = f descend
  where
    descend :: DescendM m
    descend = makeDescend ops

-- | A function that applies a generic operation.
-- This applies the operations in the set to the immediate children of the
-- provided value, but not to the value itself.
--
-- You should use this type of operation when you're writing a traversal with
-- explicit descent, and you want to descend into all the children of a value
-- that one of your transformations has been applied to.
type DescendM m = (forall t. Data t => t -> m t)

-- | As 'DescendM', but specialised for 'PassM'.
type Descend = DescendM PassM

-- | Build a 'DescendM' function from a set of operations.
makeDescend :: forall m. Monad m => OpsM m -> DescendM m
makeDescend ops@(tks, _) = gmapMFor ts recurse
  where
    ts :: TypeSet
    ts = makeTypeSet tks

    recurse :: RecurseM m
    recurse = makeRecurse ops

-- | Apply a transformation, recursing depth-first.
applyDepthM :: forall m t1 s. (Monad m, Data t1, Data s) =>
               TransformM m t1 -> s -> m s
applyDepthM f1 = makeRecurse ops
  where
    ops :: OpsM m
    ops = baseOp `extOp` makeDepth ops f1

-- | As 'applyDepthM', but for transformations that work on all 'A.Structured'
-- types.
applyDepthSM :: forall m s. (Monad m, Data s) =>
                (forall t. Data t => TransformM m (A.Structured t)) -> s -> m s
applyDepthSM f1 = makeRecurse ops
  where
    ops :: OpsM m
    ops = extOpSD baseOp ops f1

-- | Apply two transformations, recursing depth-first.
applyDepthM2 :: forall m t1 t2 s. (Monad m, Data t1, Data t2, Data s) =>
                TransformM m t1 -> TransformM m t2 -> s -> m s
applyDepthM2 f1 f2 = makeRecurse ops
  where
    ops :: OpsM m
    ops = baseOp `extOp` makeDepth ops f1
                 `extOp` makeDepth ops f2

-- | Apply a check, recursing depth-first.
checkDepthM :: forall m t1 s. (Monad m, Data t1, Data s) =>
               CheckM m t1 -> s -> m s
checkDepthM f1 = makeRecurse ops
  where
    ops :: OpsM m
    ops = baseOp `extOp` makeCheck ops f1

-- | Apply two checks, recursing depth-first.
checkDepthM2 :: forall m t1 t2 s. (Monad m, Data t1, Data t2, Data s) =>
               CheckM m t1 -> CheckM m t2 -> s -> m s
checkDepthM2 f1 f2 = makeRecurse ops
  where
    ops :: OpsM m
    ops = baseOp `extOp` makeCheck ops f1
                 `extOp` makeCheck ops f2

