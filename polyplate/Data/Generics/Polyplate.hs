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
-- advised.  Instead, you should use functions in the "GenInstances" module to automatically
-- generate source files with the appropriate instances.  Instances are generated
-- for PolyplateMRoute and PolyplateSpine.  There is a single instance for each
-- of PolyplateM and Polyplate that automatically use PolyplateMRoute.
--
-- As an example of how to use polyplate we will use the Paradise benchmark, first
-- used by Ralf Lammel for SYB.
--
-- The data-types can be found at: <http://www.cs.vu.nl/boilerplate/testsuite/paradise/CompanyDatatypes.hs>
--
-- If you view that file, you can see that the Company type contains all the other
-- types.  So to generate instances you need only do this:
--
-- > import CompanyDatatypes
-- > import Data.Generics.Polyplate.GenInstances
-- >
-- > main :: IO ()
-- > main = writeInstancesTo GenWithoutOverlapped GenOneClass
-- >          [genInstance (undefined :: Company)]
-- >          ["module Instances where"
-- >          ,"import Data.Generics.Polyplate"
-- >          ,"import Data.Generics.Polyplate.Route"
-- >          ,"import Data.Maybe"
-- >          ,"import Data.Tree"
-- >          ,"import qualified CompanyDatatypes"
-- >          ] "Instances.hs"
--
-- You must then compile the Instances module in your program, and make sure it
-- is regenerated every time CompanyDatatypes changes (see the documentation for
-- your build system).
--
-- Then you can write the function to increase salaries as follows (converting
-- from <http://www.cs.vu.nl/boilerplate/testsuite/paradise/Main.hs>):
--
-- > import CompanyDatatypes
-- > import Data.Generics.Polyplate
-- > import Data.Generics.Polyplate.Schemes
-- > import Instances
-- >
-- > increase :: Float -> Company -> Company
-- > increase k = applyBottomUp (incS k)
-- >
-- > incS :: Float -> Salary -> Salary
-- > incS k (S s) = S (s * (1+k))
-- >
-- > main = print $ increase 0.1 genCom
--
-- As well as doing transformations (both monadic and non-monadic), you can
-- also perform queries.  For this example, we will adapt another SYB example,
-- that of crushing binary trees
-- (<http://www.cs.vu.nl/boilerplate/testsuite/foldTree.hs>).  This has the
-- following data types, and example item (here renamed to avoid a conflict):
--
-- > data MyTree a w = Leaf a
-- >                 | Fork (MyTree a w) (MyTree a w)
-- >                 | WithWeight (MyTree a w) w
-- >   deriving (Typeable, Data)
-- >
-- > mytree :: MyTree Int Int
-- > mytree = Fork (WithWeight (Leaf 42) 1)
-- >               (WithWeight (Fork (Leaf 88) (Leaf 37)) 2)
--
-- The instance generation is identical to before, with the caveat with our
-- current instance generation, you can only generate instances for concrete
-- types (e.g. MyTree String Float), not for all parameterised types (e.g. MyTree
-- String a).  The SYB example then prints out two things: first it prints out
-- all Ints in the tree (thus: both weights and items), and second it prints out
-- just the values (i.e. Ints wrapped in a Leaf).  We can do the same:
--
-- > main = print ( catMaybes $ flatten $ applyQuery (id :: Int -> Int) myTree
-- >              , catMaybes $ flatten $ fmap join $ applyQuery fromLeafInt myTree
-- >              )
-- >  where
-- >    fromLeafInt :: MyTree Int Int -> Maybe Int
-- >    fromLeafInt (Leaf x) = Just x
-- >    fromLeafInt _ = Nothing
--
-- The 'applyQuery' function takes a query function that transforms items of interest
-- into query results.  In the first case, we simply pass the identity function
-- on Ints.  This will then give us a Tree (Maybe Int) of all the Ints in myTree.
--  We use flatten to flatten the tree into a list (depth-first ordering) and catMaybes
-- to filter out any Nothing results.  We could also have written this first call
-- as:
--
-- > listifyDepth (const True :: Int -> Bool) myTree
--
-- The second call gives Maybe Int as its query result, giving us a Tree (Maybe
-- (Maybe Int)).  We use fmap join to turn this into a Tree (Maybe Int) then catMaybes
-- and flatten again to get back a list.  Another way of writing the second call
-- would have been:
--
-- > [x | Leaf x <- listifyDepth isLeafInt myTree]
-- >   where
-- >     isLeaf :: MyTree Int Int -> Bool
-- >     isLeaf (Leaf _) = True
-- >     isLeaf _ = False
-- 
-- TODO include an example with routes
module Data.Generics.Polyplate (PolyplateMRoute(..), PolyplateM(..), Polyplate(..),
  makeRecurseM, RecurseM, makeRecurse, Recurse,
  makeDescendM, DescendM, makeDescend, Descend,
--  makeRecurseQ, RecurseQ,
--  makeDescendQ, DescendQ,
  BaseOp, baseOp,
  ExtOpM, extOpM, ExtOpMRoute, extOpMRoute, ExtOp, extOp, OneOpM, OneOp, TwoOpM, TwoOp
  ) where

import Control.Monad.Identity
import Data.Maybe
import Data.Tree

import Data.Generics.Polyplate.Route

-- | The main Polyplate type-class.
--
-- The first parameter is the larger\/outer type on which you want to operate.
--  If you want to operate on all Strings in a Foo, then the first parameter will
-- be Foo for the instance you want.  The fourth parameter is the monad in which
-- you wish to perform the transformation.  If you do not need a monadic transformation,
-- see 'transform' and 'Polyplate' below.  The fifth parameter is the outermost
-- type that you began modifying.
--
-- The second and third parameters are ops sets.  The empty ops list is (), the
-- unit type.  Any other ops set is written as ((a, Route a outer) -> m a, r) where a is the specific
-- type you are looking to modify, m is the monad (must be the same as the fourth
-- parameter of the type-class), outer is the same as the fifth parameter of the
-- type-class, and r is the rest of the ops set (either same
-- format, or the empty list).  Ops sets must never feature functions over a particular
-- type twice (e.g. ((String, Route String outer) -> m String, ((String, Router
-- String outer) -> m String, ()))) is not a valid
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
-- > PolyplateMRoute Foo recurse descent m outer
--
-- Then the recurse ops set is the set to apply to Foo, whereas the descent ops
-- set is the set to apply to Bar and Baz.  In particular, if your recurse ops
-- set is empty and the descent ops set is:
--
-- > ((Foo, Route Foo outer) -> m Foo, ())
--
-- Then this function will not be applied unless Foo is inside Bar or Baz.
--
-- Generally you will not use this function or type-class directly, but will instead
-- use the helper functions lower down in this module.
class Monad m => PolyplateMRoute t o o' m outer where
  transformMRoute :: o -> o' -> (t, Route t outer) -> m t

-- | A derivative of PolyplateMRoute without all the route stuff.
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
-- > PolyplateM Foo recurse descent m
--
-- Then the recurse ops set is the set to apply to Foo, whereas the descent ops
-- set is the set to apply to Bar and Baz.  In particular, if your recurse ops
-- set is empty and the descent ops set is:
--
-- > (Foo -> m Foo, ())
--
-- Then this function will not be applied unless Foo is inside Bar or Baz.
--
-- Generally you will not use this function or type-class directly, but will instead
-- use the helper functions lower down in this module.
class (Monad m) => PolyplateM t o o' m where
  transformM :: o -> o' -> t -> m t


instance (Monad m
  , PolyplateMRoute t o o' m ()
  , ConvertOpsToIgnoreRoute ro o
  , ConvertOpsToIgnoreRoute ro' o') => PolyplateM t ro ro' m where
  transformM o o' t = transformMRoute (convertOpsToIgnoreRoute o)
                                      (convertOpsToIgnoreRoute o')
                                      (t, fakeRoute t) 
    where
      fakeRoute :: t -> Route t ()
      fakeRoute = const $ error "transformM"

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

{-
type RecurseQ a opQ = forall t. PolyplateSpine t opQ () a => t -> Tree (Maybe a)
type DescendQ a opQ = forall t. PolyplateSpine t () opQ a => t -> Tree (Maybe a)


makeRecurseQ :: opQ -> RecurseQ a opQ
makeRecurseQ ops = transformSpine ops ()

makeDescendQ :: opQ -> DescendQ a opQ
makeDescendQ ops = transformSpine () ops
-}

-- | The type of the empty set of operations
type BaseOp = ()

-- | The function giving you the empty set of operations.  Helps to make your
-- code clearer, even if it's longer.
baseOp :: BaseOp
baseOp = ()

-- | The type that extends an ops set (opT) in the given monad (m) to be applied to
-- the given type (t).  You cannot mix monadic and non-monadic operations in the
-- same list.  This is for use with the 'PolyplateM' class.
type ExtOpM m opT t = (t -> m t, opT)

-- | The type that extends an ops set (opT) in the given monad (m) to be applied
-- to the given type (t) with routes to the outer type (outer).  This is for use
-- with the 'PolyplateMRoute' class.
type ExtOpMRoute m opT t outer = ((t, Route t outer) -> m t, opT)

-- | The type that extends an ops set (opT) to be applied to the given type (t).
--  You cannot mix monadic and non-monadic operations in the same list.  This is
-- for use with the 'Polyplate' class.
type ExtOp opT t = (t -> t, opT)

-- | The function that extends an ops set (opT) in the given monad (m) to be applied to
-- the given type (t).  You cannot mix monadic and non-monadic operations in the
-- same list.  This is for use with the 'PolyplateM' class.
extOpM :: opT -> (t -> m t) -> ExtOpM m opT t
extOpM ops f = (f, ops)

-- | The function that extends an ops set (opT) in the given monad (m) to be applied
-- to the given type (t) with routes to the outer type (outer).  This is for use
-- with the 'PolyplateMRoute' class.
extOpMRoute :: opT -> ((t, Route t outer) -> m t) -> ExtOpMRoute m opT t outer
extOpMRoute ops f = (f, ops)

-- | The function that extends an ops set (opT) in the given monad (m) to be applied to
-- the given type (t).  You cannot mix monadic and non-monadic operations in the
-- same list.  This is for use with the 'Polyplate' class.
extOp :: opT -> (t -> t) -> ExtOp opT t
extOp ops f = (f, ops)

-- | A handy synonym for a monadic ops set with only one item, to use with 'PolyplateM'.
type OneOpM m t = ExtOpM m BaseOp t
-- | A handy synonym for an ops set with only one item, to use with 'Polyplate'.
type OneOp t = ExtOp BaseOp t

-- | A handy synonym for a monadic ops set with only two items, to use with 'PolyplateM'.
type TwoOpM m s t = ExtOpM m (ExtOpM m BaseOp s) t
-- | A handy synonym for an ops set with only two items, to use with 'Polyplate'.
type TwoOp s t = ExtOp (ExtOp BaseOp s) t


-- {{{ Various type-level programming ops conversions:

-- | A helper class to convert non-monadic transformations into monadic ones in
-- the Identity monad.
class ConvertOpsToIdentity o o' | o -> o' where
  convertOpsToIdentity :: o -> o'

instance ConvertOpsToIdentity () () where
  convertOpsToIdentity = id

instance ConvertOpsToIdentity r r' => ConvertOpsToIdentity (a -> a, r) (a -> Identity a, r') where
  convertOpsToIdentity (f, r) = (return . f, convertOpsToIdentity r)

{-
-- | A helper class to convert operation lists to have FullSpine at their base
-- rather than BaseOp
class ConvertSpineOpsToFull a o o' | a o -> o' where
  convertSpineOpsToFull :: a -> o -> o'

instance ConvertSpineOpsToFull a () (FullSpine a) where
  convertSpineOpsToFull def _ = FullSpine def

instance ConvertSpineOpsToFull b r r' => ConvertSpineOpsToFull b (a, r) (a, r') where
  convertSpineOpsToFull def (f, r) = (f, convertSpineOpsToFull def r)
-}

-- | A helper class to convert operations not expecting a route to those that ignore
-- the route (which will have the unit type as its outer type).
class ConvertOpsToIgnoreRoute o o' | o -> o' where
  convertOpsToIgnoreRoute :: o -> o'

instance ConvertOpsToIgnoreRoute () () where
  convertOpsToIgnoreRoute = id

instance ConvertOpsToIgnoreRoute r r' =>
  ConvertOpsToIgnoreRoute (t -> m t, r) ((t, Route t ()) -> m t, r') where
  convertOpsToIgnoreRoute (f, r) = (f . fst, convertOpsToIgnoreRoute r)


-- }}}
