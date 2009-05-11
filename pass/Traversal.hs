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
  , ExtOpMS, ExtOpMSP, extOpMS, opMS, PassOnStruct, PassASTOnStruct
  , applyBottomUpMS, ASTStructured
  , RecurseM, DescendM, BaseOpM, baseOpM, OneOpM, TwoOpM, BaseOpMRoute, baseOpMRoute, OneOpMRoute
  , module Data.Generics.Alloy
  , module Data.Generics.Alloy.Schemes
  ) where

import Control.Monad.State
import Data.Generics (Data)
import Data.Generics.Alloy
import Data.Generics.Alloy.Schemes


import qualified AST as A
import NavAST()
import Pass

type RecurseM a b = RecurseA a b
type DescendM a b = DescendA a b
type BaseOpM = BaseOpA
type BaseOpMRoute = BaseOpARoute
type OneOpM s = OneOpA s
type OneOpMRoute s = OneOpARoute s
type TwoOpM s t = TwoOpA s t
baseOpM :: BaseOpM m
baseOpM = baseOpA
baseOpMRoute :: BaseOpMRoute m outer
baseOpMRoute = baseOpARoute

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

type ExtOpMS opT =
          (A.Structured ()) :-*
          (A.Structured A.Alternative) :-*
          (A.Structured A.Choice) :-*
          (A.Structured A.ExpressionList) :-*
          (A.Structured A.Option) :-*
          (A.Structured A.Process) :-*
          (A.Structured A.Variant) :-*
          opT

type ExtOpMSP opT = ExtOpMS opT PassM

type PassOnStruct = PassOnOps (ExtOpMS BaseOpA)
type PassASTOnStruct = PassASTOnOps (ExtOpMS BaseOpA)

class (AlloyA (A.Structured a) BaseOpA opsM
      ,AlloyA (A.Structured a) opsM BaseOpA
      ,Data a
      ,Monad m
      ) => ASTStructured a opsM m opsQ r

instance (AlloyA (A.Structured ()) BaseOpA opsM
         ,AlloyA (A.Structured ()) opsM BaseOpA
         ,Monad m) => ASTStructured () opsM m opsQ r

instance (AlloyA (A.Structured A.Alternative) BaseOpA opsM
         ,AlloyA (A.Structured A.Alternative) opsM BaseOpA
         ,Monad m) => ASTStructured A.Alternative opsM m opsQ r

instance (AlloyA (A.Structured A.Choice) BaseOpA opsM
         ,AlloyA (A.Structured A.Choice) opsM BaseOpA
         ,Monad m) => ASTStructured A.Choice opsM m opsQ r

instance (AlloyA (A.Structured A.ExpressionList) BaseOpA opsM
         ,AlloyA (A.Structured A.ExpressionList) opsM BaseOpA
         ,Monad m) => ASTStructured A.ExpressionList opsM m opsQ r

instance (AlloyA (A.Structured A.Option) BaseOpA opsM
         ,AlloyA (A.Structured A.Option) opsM BaseOpA
         ,Monad m) => ASTStructured A.Option opsM m opsQ r

instance (AlloyA (A.Structured A.Process) BaseOpA opsM
         ,AlloyA (A.Structured A.Process) opsM BaseOpA
         ,Monad m) => ASTStructured A.Process opsM m opsQ r

instance (AlloyA (A.Structured A.Variant) BaseOpA opsM
         ,AlloyA (A.Structured A.Variant) opsM BaseOpA
         ,Monad m) => ASTStructured A.Variant opsM m opsQ r


extOpMS :: forall m opT op0T.
          (AlloyA (A.Structured ()) BaseOpA op0T,
           AlloyA (A.Structured A.Alternative) BaseOpA op0T,
           AlloyA (A.Structured A.Choice) BaseOpA op0T,
           AlloyA (A.Structured A.ExpressionList) BaseOpA op0T,
           AlloyA (A.Structured A.Option) BaseOpA op0T,
           AlloyA (A.Structured A.Process) BaseOpA op0T,
           AlloyA (A.Structured A.Variant) BaseOpA op0T,
           AlloyA (A.Structured ()) op0T BaseOpA,
           AlloyA (A.Structured A.Alternative) op0T BaseOpA,
           AlloyA (A.Structured A.Choice) op0T BaseOpA,
           AlloyA (A.Structured A.ExpressionList) op0T BaseOpA,
           AlloyA (A.Structured A.Option) op0T BaseOpA,
           AlloyA (A.Structured A.Process) op0T BaseOpA,
           AlloyA (A.Structured A.Variant) op0T BaseOpA,
           Monad m) =>
          opT m ->
          -- Pairing the next two arguments allows us to apply this function infix:
          (op0T m, -- just a type witness
           forall t. ASTStructured t op0T m () () => A.Structured t -> m (A.Structured t)) ->
          ExtOpMS opT m
extOpMS ops (_, f)
    = f :-* f :-* f :-* f :-* f :-* f :-* f :-* ops

opMS :: forall m op0T.
          (AlloyA (A.Structured ()) BaseOpA op0T,
           AlloyA (A.Structured A.Alternative) BaseOpA op0T,
           AlloyA (A.Structured A.Choice) BaseOpA op0T,
           AlloyA (A.Structured A.ExpressionList) BaseOpA op0T,
           AlloyA (A.Structured A.Option) BaseOpA op0T,
           AlloyA (A.Structured A.Process) BaseOpA op0T,
           AlloyA (A.Structured A.Variant) BaseOpA op0T,
           AlloyA (A.Structured ()) op0T BaseOpA,
           AlloyA (A.Structured A.Alternative) op0T BaseOpA,
           AlloyA (A.Structured A.Choice) op0T BaseOpA,
           AlloyA (A.Structured A.ExpressionList) op0T BaseOpA,
           AlloyA (A.Structured A.Option) op0T BaseOpA,
           AlloyA (A.Structured A.Process) op0T BaseOpA,
           AlloyA (A.Structured A.Variant) op0T BaseOpA,
           Monad m) =>
          -- Pairing the next two arguments allows us to apply this function infix:
          (op0T m, -- just a type witness
           forall t. ASTStructured t op0T m () () => A.Structured t -> m (A.Structured t)) ->
          ExtOpMS BaseOpA m
opMS x = extOpMS baseOpA x

applyBottomUpMS :: (AlloyA t (ExtOpMS BaseOpA) BaseOpA) =>
  (forall a. (Data a, AlloyA (A.Structured a) BaseOpA (ExtOpMS BaseOpA)) =>
     (A.Structured a -> PassM (A.Structured a)))
  -> t -> PassM t
applyBottomUpMS f = makeRecurseM ops
  where
    ops = baseOpA `extOpMS` (ops, makeBottomUpM ops f)

type TransformStructured ops
  = (AlloyA (A.Structured t) BaseOpA ops, Data t) => Transform (A.Structured t)

type TransformStructured' ops
  = (AlloyA (A.Structured t) BaseOpA ops
    ,AlloyA (A.Structured t) ops BaseOpA, Data t) => Transform (A.Structured t)

type TransformStructuredM' m ops
  = (AlloyA (A.Structured t) BaseOpA ops
    ,AlloyA (A.Structured t) ops BaseOpA, Data t) => A.Structured t -> m (A.Structured t)
