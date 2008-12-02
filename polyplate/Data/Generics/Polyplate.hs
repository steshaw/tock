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

-- | This is the primary module for the polyplate library, that declares the type-class
-- and methods that use it.
--
-- Polyplate is a generic programming system for automatically traversing data
-- structures, operating on specific types within that structure.
--
-- TODO examples
--
-- Instances of the PolyplateM type-class /can/ be written manually but it's not
-- advised.  Instead, you should use functions in the "GenPolyplate" module to automatically
-- generate source files with the appropriate instances.
module Data.Generics.Polyplate (PolyplateM(..), Polyplate(..),
  makeRecurseM, RecurseM,
  makeDescendM, DescendM,
  BaseOp, baseOp,
  ExtOpM, extOpM, ExtOp, extOp, OneOpM, OneOp, TwoOpM, TwoOp) where

import Control.Monad.Identity

-- | The main Polyplate type-class.
--
-- The first parameter is the larger\/outer type on which you want to operate.
--  If you want to operate on all Strings in a Foo, then the first parameter will
-- be Foo for the instance you want.  The fourth parameter is the monad in which
-- you wish to perform the transformation.  If you do not need a monadic transformation,
-- see 'transform' and 'Polyplate' below.
--
-- The second and third parameters are ops sets.  The empty ops list is (), the
-- unit type.  Any other ops set is written as (a -> m a, r) where a is the specific
-- type you are looking to modify, m is the monad (must be the same as the fourth
-- parameter of the type-class), and r is the rest of the ops set (either same
-- format, or the empty list).  Ops sets must never feature functions over a particular
-- type twice (e.g. (String -> m String, (String -> m String, ()))) is not a valid
-- ops set.
--
-- The second parameter is the /recurse/ ops set to apply directly to the
-- type, whereas the third parameter is the /descent/ ops set to apply to its
-- children.  So for example, if you have a type:
--
-- > data Foo = Foo { bar :: Bar, baz :: Baz}
--
-- and:
--
-- > Polyplate Foo recurse descent m
--
-- Then the recurse ops set is the set to apply to Foo, whereas the descent ops
-- set is the set to apply to Bar.  In particular, if your descent ops set is:
--
-- > (Foo -> m Foo, ())
--
-- Then this function will not be applied unless Foo is inside Bar or Baz.
--
-- Generally you will not use this function or type-class directly, but will instead
-- use the helper functions lower down in this module.
class Monad m => PolyplateM t o o' m where
  transformM :: o -> o' -> t -> m t


-- | A helper class to convert non-monadic transformations into monadic ones in
-- the Identity monad.
class ConvertOpsToIdentity o o' | o -> o' where
  convertOpsToIdentity :: o -> o'

instance ConvertOpsToIdentity () () where
  convertOpsToIdentity = id

instance ConvertOpsToIdentity r r' => ConvertOpsToIdentity (a -> a, r) (a -> Identity a, r') where
  convertOpsToIdentity (f, r) = (return . f, convertOpsToIdentity r)

-- | A non-monadic equivalent of PolyplateM.  All ops sets are of the form:
--
-- > (a -> a, (b -> b, ()))
class Polyplate t o o' where
  transform :: o -> o' -> t -> t

instance (PolyplateM t mo mo' Identity, ConvertOpsToIdentity o mo, ConvertOpsToIdentity o' mo') => Polyplate t o o' where
  transform o o' t = runIdentity (transformM (convertOpsToIdentity o) (convertOpsToIdentity o') t)

-- | A type representing a recursive monadic modifier function that applies the given ops
-- (in the given monad) directly to the given type.
type RecurseM m opT = forall t. PolyplateM t opT () m => t -> m t

-- | Given a set of operations (as described in the 'PolyplateM' type-class),
-- makes a recursive modifier function.
makeRecurseM :: Monad m => opT -> RecurseM m opT
makeRecurseM ops = transformM ops ()

type DescendM m opT = forall t. PolyplateM t () opT m => t -> m t

makeDescendM :: Monad m => opT -> DescendM m opT
makeDescendM ops = transformM () ops

-- | The type of the empty set of operations
type BaseOp = ()

-- | The function giving you the empty set of operations.  Helps to make your
-- code clearer, even if it's longer.
baseOp :: BaseOp
baseOp = ()

-- | The type that extends an ops set (opT) in the given monad (m) to be applied to
-- the given type (t).  You cannot mix monadic and non-monadic operations in the
-- same list.
type ExtOpM m opT t = (t -> m t, opT)

-- | The type that extends an ops set (opT) to be applied to the given type (t).
--  You cannot mix monadic and non-monadic operations in the same list.
type ExtOp opT t = (t -> t, opT)

-- | The function that extends an ops set (opT) in the given monad (m) to be applied to
-- the given type (t).  You cannot mix monadic and non-monadic operations in the
-- same list.
extOpM :: opT -> (t -> m t) -> ExtOpM m opT t
extOpM ops f = (f, ops)

-- | The function that extends an ops set (opT) in the given monad (m) to be applied to
-- the given type (t).  You cannot mix monadic and non-monadic operations in the
-- same list.
extOp :: opT -> (t -> t) -> ExtOp opT t
extOp ops f = (f, ops)

-- | A handy synonym for an ops set with only one item.
type OneOpM m t = ExtOpM m BaseOp t
-- | A handy synonym for an ops set with only one item.
type OneOp t = ExtOp BaseOp t

-- | A handy synonym for an ops set with only two items.
type TwoOpM m s t = ExtOpM m (ExtOpM m BaseOp s) t
-- | A handy synonym for an ops set with only two items.
type TwoOp s t = ExtOp (ExtOp BaseOp s) t

