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

-- | Traversal strategies over the AST and other data types.  This is now mainly
-- a collection of extra Tock-specific utilities that go on top of Polyplate
module Traversal (
    TransformM, Transform, TransformStructured, TransformStructured', TransformStructuredM'
  , CheckM, Check
  , ExtOpMP, ExtOpMS, ExtOpMSP, extOpMS, PassOnStruct, PassASTOnStruct
  , ExtOpQS, extOpQS
  , applyBottomUpMS, ASTStructured
  , module Data.Generics.Polyplate
  , module Data.Generics.Polyplate.Schemes
  ) where

import Control.Monad.State
import Data.Generics (Data)
import Data.Generics.Polyplate
import Data.Generics.Polyplate.Schemes


import qualified AST as A
import NavAST()
import NavASTSpine()
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

type PassOnStruct = PassOnOps (ExtOpMSP BaseOp)
type PassASTOnStruct = PassASTOnOps (ExtOpMSP BaseOp)

class (PolyplateM (A.Structured a) () opsM m
      ,PolyplateM (A.Structured a) opsM () m
      ,PolyplateSpine (A.Structured a) opsQ () r
      ,PolyplateSpine (A.Structured a) () opsQ r
      ,Data a
      ,Monad m
      ) => ASTStructured a opsM m opsQ r

instance (PolyplateM (A.Structured ()) () opsM m
         ,PolyplateM (A.Structured ()) opsM () m
         ,PolyplateSpine (A.Structured ()) opsQ () r
         ,PolyplateSpine (A.Structured ()) () opsQ r
         ,Monad m) => ASTStructured () opsM m opsQ r

instance (PolyplateM (A.Structured A.Alternative) () opsM m
         ,PolyplateM (A.Structured A.Alternative) opsM () m
         ,PolyplateSpine (A.Structured A.Alternative) opsQ () r
         ,PolyplateSpine (A.Structured A.Alternative) () opsQ r
         ,Monad m) => ASTStructured A.Alternative opsM m opsQ r

instance (PolyplateM (A.Structured A.Choice) () opsM m
         ,PolyplateM (A.Structured A.Choice) opsM () m
         ,PolyplateSpine (A.Structured A.Choice) opsQ () r
         ,PolyplateSpine (A.Structured A.Choice) () opsQ r
         ,Monad m) => ASTStructured A.Choice opsM m opsQ r

instance (PolyplateM (A.Structured A.ExpressionList) () opsM m
         ,PolyplateM (A.Structured A.ExpressionList) opsM () m
         ,PolyplateSpine (A.Structured A.ExpressionList) opsQ () r
         ,PolyplateSpine (A.Structured A.ExpressionList) () opsQ r
         ,Monad m) => ASTStructured A.ExpressionList opsM m opsQ r

instance (PolyplateM (A.Structured A.Option) () opsM m
         ,PolyplateM (A.Structured A.Option) opsM () m
         ,PolyplateSpine (A.Structured A.Option) opsQ () r
         ,PolyplateSpine (A.Structured A.Option) () opsQ r
         ,Monad m) => ASTStructured A.Option opsM m opsQ r

instance (PolyplateM (A.Structured A.Process) () opsM m
         ,PolyplateM (A.Structured A.Process) opsM () m
         ,PolyplateSpine (A.Structured A.Process) opsQ () r
         ,PolyplateSpine (A.Structured A.Process) () opsQ r
         ,Monad m) => ASTStructured A.Process opsM m opsQ r

instance (PolyplateM (A.Structured A.Variant) () opsM m
         ,PolyplateM (A.Structured A.Variant) opsM () m
         ,PolyplateSpine (A.Structured A.Variant) opsQ () r
         ,PolyplateSpine (A.Structured A.Variant) () opsQ r
         ,Monad m) => ASTStructured A.Variant opsM m opsQ r


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
           forall t. ASTStructured t op0T m () () => A.Structured t -> m (A.Structured t)) ->
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

type ExtOpQS r opT =
          (A.Structured () -> r,
          (A.Structured A.Alternative -> r,
          (A.Structured A.Choice -> r,
          (A.Structured A.ExpressionList -> r,
          (A.Structured A.Option -> r,
          (A.Structured A.Process -> r,
          (A.Structured A.Variant -> r,
          opT)))))))

extOpQS :: forall m opT op0T r.
          (PolyplateSpine (A.Structured ()) () op0T r,
           PolyplateSpine (A.Structured A.Alternative) () op0T r,
           PolyplateSpine (A.Structured A.Choice) () op0T r,
           PolyplateSpine (A.Structured A.ExpressionList) () op0T r,
           PolyplateSpine (A.Structured A.Option) () op0T r,
           PolyplateSpine (A.Structured A.Process) () op0T r,
           PolyplateSpine (A.Structured A.Variant) () op0T r,
           PolyplateSpine (A.Structured ()) op0T () r,
           PolyplateSpine (A.Structured A.Alternative) op0T () r,
           PolyplateSpine (A.Structured A.Choice) op0T () r,
           PolyplateSpine (A.Structured A.ExpressionList) op0T () r,
           PolyplateSpine (A.Structured A.Option) op0T () r,
           PolyplateSpine (A.Structured A.Process) op0T () r,
           PolyplateSpine (A.Structured A.Variant) op0T () r) =>
          opT ->
          -- Pairing the next two arguments allows us to apply this function infix:
          (op0T, -- just a type witness
           forall t. ASTStructured t () PassM op0T r => A.Structured t -> r) ->
          ExtOpQS r opT
extOpQS ops (_, f)
    = ops
      `extOpQ` (f :: A.Structured A.Variant -> r)
      `extOpQ` (f :: A.Structured A.Process -> r)
      `extOpQ` (f :: A.Structured A.Option -> r)
      `extOpQ` (f :: A.Structured A.ExpressionList -> r)
      `extOpQ` (f :: A.Structured A.Choice -> r)
      `extOpQ` (f :: A.Structured A.Alternative -> r)
      `extOpQ` (f :: A.Structured () -> r)


applyBottomUpMS :: (PolyplateM t (ExtOpMSP BaseOp) () PassM) =>
  (forall a. (Data a, PolyplateM (A.Structured a) () (ExtOpMSP BaseOp) PassM) =>
     (A.Structured a -> PassM (A.Structured a)))
  -> t -> PassM t
applyBottomUpMS f = makeRecurseM ops
  where
    ops = baseOp `extOpMS` (ops, makeBottomUpM ops f)

type TransformStructured ops
  = (PolyplateM (A.Structured t) () ops PassM, Data t) => Transform (A.Structured t)

type TransformStructured' ops
  = (PolyplateM (A.Structured t) () ops PassM
    ,PolyplateM (A.Structured t) ops () PassM , Data t) => Transform (A.Structured t)

type TransformStructuredM' m ops
  = (PolyplateM (A.Structured t) () ops m
    ,PolyplateM (A.Structured t) ops () m , Data t) => A.Structured t -> m (A.Structured t)
