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
module Data.Generics.Polyplate (PolyplateM(..), Polyplate(..), PolyplateSpine(..),
  makeRecurseM, RecurseM, makeRecurse, Recurse,
  makeDescendM, DescendM, makeDescend, Descend,
  BaseOp, baseOp,
  ExtOpM, extOpM, ExtOp, extOp, OneOpM, OneOp, TwoOpM, TwoOp) where

import Control.Monad.Identity

import Data.Tree

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
  transformM :: o -> o' -> t -> m t -- TODO add routes

  -- List of use cases for the Polyplate type-class, to try to decide best on its
  -- necessary functions:
  --
  -- 1. To perform a monadic modification on specific types in the ops across a
  -- whole structure.
  -- 2. As #1, but non-monadic (use Identity monad to adapt the above)
  -- 3. To perform a query across the whole tree that returns a rose-tree that reflects
  -- the (spine-view) structure of the data.
  -- 4. As #3, but to return a flattened list (use flatten to adapt the above)
  -- 5. To perform a monadic modification that also uses modification wrappers,
  -- (a more general case of #1)
  --
  -- So I think there are two classes needed:
  --
  -- * One to apply monadic transformations that takes routes (covers #5, #2, #1)
  -- 
  -- * One to apply tree-based queries that transform a whole data structure into
  -- its tree spine-view, with optional methods for flattening into a depth-first
  -- or breadth-first order.

class PolyplateSpine t o o' a where
  transformSpine :: o -> o' -> t -> Tree (Maybe a)


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

-- | A type representing a monadic modifier function that applies the given ops
-- (opT) in the given monad (m) directly to the given type (t).
type RecurseM m opT = forall t. PolyplateM t opT () m => t -> m t

-- | Given a set of operations (as described in the 'PolyplateM' type-class),
-- makes a recursive modifier function.
makeRecurseM :: Monad m => opT -> RecurseM m opT
makeRecurseM ops = transformM ops ()

-- | A type representing a monadic modifier function that applies the given ops
-- (opT) in the given monad (m) to the children of the given type (t).
type DescendM m opT = forall t. PolyplateM t () opT m => t -> m t

-- | Given a set of operations (as described in the 'PolyplateM' type-class),
-- makes a descent modifier function that applies the operation to the type's children.
makeDescendM :: Monad m => opT -> DescendM m opT
makeDescendM ops = transformM () ops

-- | A type representing a modifier function that applies the given ops
-- (opT) directly to the given type (t).
type Recurse opT = forall t. Polyplate t opT () => t -> t

-- | Given a set of operations (as described in the 'Polyplate' type-class),
-- makes a modifier function that applies the operations directly.
makeRecurse :: opT -> Recurse opT
makeRecurse ops = transform ops ()

-- | A type representing a modifier function that applies the given ops
-- (opT) to the children of the given type (t).
type Descend opT = forall t. Polyplate t () opT => t -> t

-- | Given a set of operations (as described in the 'PolyplateM' type-class),
-- makes a descent modifier function that applies the operation to the type's children.
makeDescend :: opT -> Descend opT
makeDescend ops = transform () ops


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

