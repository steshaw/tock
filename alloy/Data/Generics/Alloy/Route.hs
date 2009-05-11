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
module Data.Generics.Polyplate.Route
  (Route, routeModify, routeGet, routeSet, (@->), identityRoute, routeId, routeList,
    makeRoute, routeDataMap, routeDataSet)
  where

import Control.Monad.Identity
import Control.Monad.State

import qualified Data.Map as Map
import qualified Data.Set as Set

-- | A Route is a way of navigating to a particular node in a tree structure.
--
-- Let's say that you have some binary tree structure:
--
-- > data BinTree a = Leaf a | Branch (BinTree a) (BinTree a)
--
-- Suppose you then have a big binary tree of integers, potentially with duplicate values,
-- and you want to be able to modify a particular integer.  You can't modify in-place,
-- because this is a functional language.  So you instead want to be able to apply
-- a modify function to the whole tree that really just modifies the particular
-- integer, deep within the tree.
--
-- To do this you can use a route:
-- 
-- > myRoute :: Route Int (BinTree Int)
--
-- You apply it as follows (for example, to increment the integer):
--
-- > runIdentity $ routeModify myRoute (return . (+1)) myTree
--
-- The modifier is monadic because that's usually how we want to use it, but we
-- can use the identity monad as above for pure functions.  This will only work
-- if the route is valid on the given tree.
--
-- The usual way that you get routes is via the traversal functions in the "Data.Generics.Polyplate"
-- module.
--
-- Another useful aspect is composition.  If your tree was in a tree of trees:
--
-- > routeToInnerTree :: Route (BinTree Int) (BinTree (BinTree Int))
--
-- You could compose this with the earlier route:
-- 
-- > routeToInnerTree @-> myRoute :: Route Int (BinTree (BinTree Int))
-- 
-- These routes are a little like zippers, but (in my opinion) easier to use, and
-- tack on to existing code with complex data structures (without needing any code
-- generation).  You can either compose routes yourself (as the flow-graph building
-- in Tock does) or by using the Polyplate traversals.
--
-- Routes support Eq, Show and Ord.  All these instances represent a route as a
-- list of integers: a route-map.  [0,2,1] means first child (zero-based), then
-- third child, then second child of the given data-type.  Routes are ordered using
-- the standard list ordering (lexicographic) over this representation.
data Route inner outer = Route [Int] (forall m. Monad m => (inner -> m inner) -> (outer -> m outer))

instance Eq (Route inner outer) where
  (==) (Route xns _) (Route yns _) = xns == yns

instance Ord (Route inner outer) where
  compare (Route xns _) (Route yns _) = compare xns yns

instance Show (Route inner outer) where
  show (Route ns _) = "Route " ++ show ns

-- | Gets the integer-list version of a route.  See the documentation of 'Route'.
routeId :: Route inner outer -> [Int]
routeId (Route ns _) = ns

-- | Given an index (zero is the first item), forms a route to that index item
-- in the list.  So for example:
--
-- > runIdentity $ routeModify (routeList 3) (return . (*10)) [0,1,2,3,4,5] == [0,1,2,30,4,5]
-- 
routeList :: Int -> Route a [a]
routeList 0 = Route [0] (\f (x:xs) -> f x >>= (\x' -> return (x': xs)))
routeList n = Route [1] (\f (x:xs) -> f xs >>= (\xs' -> return (x:xs'))) @-> routeList (n-1)

-- | Constructs a Route to the key-value pair at the given index (zero-based) in
-- the ordered map.  Routes involving maps are difficult because Map hides its
-- internal representation.  This route secretly boxes the Map into a list of pairs
-- and back again when used.  The identifiers for map entries (as used in the integer
-- list) are simply the index into the map as passed to this function.
routeDataMap :: Ord k => Int -> Route (k, v) (Map.Map k v)
routeDataMap n = Route [n] (\f m -> let (pre, x:post) = splitAt n (Map.toList m)
  in do x' <- f x
        return $ Map.fromList $ pre ++ (x':post))

-- | Constructs a Route to the value at the given index (zero-based) in the ordered
-- set.  See the documentation for 'routeDataMap', which is nearly identical to
-- this function.
routeDataSet :: Ord k => Int -> Route k (Set.Set k)
routeDataSet n = Route [n] (\f m -> let (pre, x:post) = splitAt n (Set.toList m)
  in do x' <- f x
        return $ Set.fromList $ pre ++ (x':post))


-- | Applies a monadic modification function using the given route.
routeModify :: Monad m => Route inner outer -> (inner -> m inner) -> (outer -> m
  outer)
routeModify (Route _ wrap) = wrap

-- | Given a route, gets the value in the large data structure that is pointed
-- to by that route.
routeGet :: Route inner outer -> outer -> inner
routeGet route = flip execState undefined . routeModify route (\x -> put x >> return x)

-- | Given a route, sets the value in the large data structure that is pointed
-- to by that route.
routeSet :: Route inner outer -> inner -> outer -> outer
routeSet route x = runIdentity . routeModify route (const $ return x)

-- | Composes two routes together.  The outer-to-mid route goes on the left hand
-- side, and the mid-to-inner goes on the right hand side to form an outer-to-inner
-- route.
(@->) :: Route mid outer -> Route inner mid -> Route inner outer
(@->) (Route outInds outF) (Route inInds inF) = Route (outInds ++ inInds) (outF
  . inF)

-- | The identity route.  This has various obvious properties:
--
-- > routeGet identityRoute == id
-- > routeSet identityRoute == const
-- > routeModify identityRoute == id
-- > identityRoute @-> route == route
-- > route @-> identityRoute == route
identityRoute :: Route a a
identityRoute = Route [] id

-- | Given the integer list of identifiers and the modification function, forms
-- a Route.  It is up to you to make sure that the integer list is valid as described
-- in the documentation of 'Route', otherwise routes constructed this way and via
-- Polyplate may exhibit strange behaviours when compared.
makeRoute :: [Int] -> (forall m. Monad m => (inner -> m inner) -> (outer -> m outer))
  -> Route inner outer
makeRoute = Route
