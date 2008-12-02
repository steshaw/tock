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
    TransformM, Transform
  , CheckM, Check
  , ExtOpMP, ExtOpMS, ExtOpMSP, extOpMS
  , module Data.Generics.Polyplate
  , module Data.Generics.Polyplate.Schemes
  ) where

import Control.Monad.State
import Data.Generics
import Data.Generics.Polyplate
import Data.Generics.Polyplate.Schemes


import qualified AST as A
import GenericUtils
import NavAST
import Pass

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

type ExtOpMP opT t = ExtOpM PassM opT t

type ExtOpMS m opT =
          (A.Structured () -> m (A.Structured ()),
          (A.Structured A.Alternative -> m (A.Structured A.Alternative),
          (A.Structured A.Choice -> m (A.Structured A.Choice),
          (A.Structured A.ExpressionList -> m (A.Structured A.ExpressionList),
          (A.Structured A.Option -> m (A.Structured A.Option),
          (A.Structured A.Process -> m (A.Structured A.Process),
          (A.Structured A.Variant -> m (A.Structured A.Variant),
          opT)))))))
type ExtOpMSP opT = ExtOpMS PassM opT

extOpMS :: forall m opT op0T.
          (PolyplateM (A.Structured ()) () op0T m,
           PolyplateM (A.Structured A.Alternative) () op0T m,
           PolyplateM (A.Structured A.Choice) () op0T m,
           PolyplateM (A.Structured A.ExpressionList) () op0T m,
           PolyplateM (A.Structured A.Option) () op0T m,
           PolyplateM (A.Structured A.Process) () op0T m,
           PolyplateM (A.Structured A.Variant) () op0T m,
           PolyplateM (A.Structured ()) op0T () m,
           PolyplateM (A.Structured A.Alternative) op0T () m,
           PolyplateM (A.Structured A.Choice) op0T () m,
           PolyplateM (A.Structured A.ExpressionList) op0T () m,
           PolyplateM (A.Structured A.Option) op0T () m,
           PolyplateM (A.Structured A.Process) op0T () m,
           PolyplateM (A.Structured A.Variant) op0T () m) =>
          opT ->
          -- Pairing the next two arguments allows us to apply this function infix:
          (op0T, -- just a type witness
           forall t. (Data t, PolyplateM (A.Structured t) () op0T m
                            , PolyplateM (A.Structured t) op0T () m) =>
           A.Structured t -> m (A.Structured t)) ->
          ExtOpMS m opT
extOpMS ops (_, f)
    = ops
      `extOpM` (f :: A.Structured A.Variant -> m (A.Structured A.Variant))
      `extOpM` (f :: A.Structured A.Process -> m (A.Structured A.Process))
      `extOpM` (f :: A.Structured A.Option -> m (A.Structured A.Option))
      `extOpM` (f :: A.Structured A.ExpressionList -> m (A.Structured A.ExpressionList))
      `extOpM` (f :: A.Structured A.Choice -> m (A.Structured A.Choice))
      `extOpM` (f :: A.Structured A.Alternative -> m (A.Structured A.Alternative))
      `extOpM` (f :: A.Structured () -> m (A.Structured ()))

