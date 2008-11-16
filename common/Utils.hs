{-
Tock: a compiler for parallel languages
Copyright (C) 2007  University of Kent

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

-- | Utility functions that aren't inherently related to Tock -- i.e. things
-- that could be put into the standard library.
module Utils where

import Control.Monad.State
import Data.Array.IArray
import Data.List
import Data.Generics (Data)
import Data.Graph.Inductive
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import qualified Data.Set as Set
import System.IO
import System.IO.Error
import Text.Regex

-- | Split the directory and file components of a path.
splitPath :: String -> (String, String)
splitPath path
    = case matchRegex dirRE path of
        Just [dir, base] -> (if dir == "" then "." else dir, base)
  where
    dirRE = mkRegex "^(.*/)?([^/]*)$"

-- | Return the directory containing a path.
dirnamePath :: String -> String
dirnamePath = fst . splitPath

-- | Return a path without any leading directory components.
basenamePath :: String -> String
basenamePath = snd . splitPath

-- | Join a relative path to an existing path (i.e. if you're given foo/bar and
-- baz, return foo/baz).
joinPath :: String -> String -> String
joinPath base new
    = case dirnamePath base of
        "." -> new
        dir -> dir ++ new

-- | Given a monadic action wrapped in a `Maybe`, run it if there's one there;
-- if it's `Nothing`, then do nothing.
doMaybe :: Monad m => Maybe (m ()) -> m ()
doMaybe (Just a) = a
doMaybe Nothing = return ()

-- | Transforms between two `Either` types using the appropriate convert
-- function:
transformEither :: (a -> c) -> (b -> d) -> Either a b -> Either c d
transformEither funcLeft funcRight x = case x of
  Left l -> Left (funcLeft l)
  Right r -> Right (funcRight r)

-- | Splits a list of Either values into two lists (the list of Lefts and the list of Rights)
splitEither :: [Either a b] -> ([a],[b])
splitEither []             = ([],[])
splitEither ((Left x):es)  = let (ls,rs) = splitEither es in (x:ls,rs)
splitEither ((Right y):es) = let (ls,rs) = splitEither es in (ls,y:rs)

-- | Transforms between two 'Maybe' types using a function:
transformMaybe :: (a -> b) -> Maybe a -> Maybe b
--transformMaybe _ Nothing = Nothing
--transformMaybe f (Just x) = Just (f x)
transformMaybe = liftM

-- | Try an IO operation, returning `Nothing` if it fails.
maybeIO :: IO a -> IO (Maybe a)
maybeIO op = catch (op >>= (return . Just)) (\e -> return Nothing)

-- | Remove a number of items from the start and end of a list.
chop :: Int -> Int -> [a] -> [a]
chop start end s = drop start (take (length s - end) s)

-- | Transform two Maybe items into a Maybe tuple, which is only Just if both inputs are Just.
mergeMaybe :: Maybe x -> Maybe y -> Maybe (x,y)
mergeMaybe Nothing _ = Nothing
mergeMaybe _ Nothing = Nothing
mergeMaybe (Just x) (Just y) = Just (x,y)

-- | Reverses a pair.
revPair :: (x,y) -> (y,x)
revPair (a,b) = (b,a)

-- | Turn one item into a (duplicate) pair.
mkPair :: a -> (a,a)
mkPair x = (x,x)

-- | Maps a function onto all inner pairs in a list.
mapPairs :: (a -> a -> b) -> [a] -> [b]
mapPairs _ [] = []
mapPairs _ [x] = []
mapPairs f (x0:(x1:xs)) = (f x0 x1) : (mapPairs f (x1:xs))

-- | Given a list of comparisons in order major->minor, returns the resultant ordering
combineCompare :: [Ordering] -> Ordering
combineCompare [] = EQ
combineCompare (LT:_) = LT
combineCompare (GT:_) = GT
combineCompare (EQ:os) = combineCompare os

-- | Maps two functions over members of a pair
transformPair :: (x -> a) -> (y -> b) -> (x,y) -> (a,b)
transformPair f g (x,y) = (f x, g y)

-- | Maps three functions over members of a triple
transformTriple :: (x -> a) -> (y -> b) -> (z -> c) -> (x,y,z) -> (a,b,c)
transformTriple f g h (x,y,z) = (f x, g y, h z)

-- | Maps four functions over members of a quadtuple
transformQuad :: (x -> a) -> (y -> b) -> (z -> c) -> (z' -> d) -> (x,y,z,z') -> (a,b,c,d)
transformQuad f g h i (x,y,z,z') = (f x, g y, h z, i z')

-- | Pipes a monadic return through a non-monadic transformation function:
(>>*) :: Monad m => m a -> (a -> b) -> m b
(>>*) v f = v >>= (return . f)

-- | Folds a list of modifier functions into a single function
foldFuncs :: [a -> a] -> a -> a
foldFuncs = foldl (.) id

-- | Folds a list of monadic modifier functions into a single function
foldFuncsM :: Monad m => [a -> m a] -> a -> m a
foldFuncsM = foldl (<.<) return

-- | Like the reflection of map.  Instead of one function and multiple data,
-- we have multiple functions and one data.
applyAll :: a -> [a -> b] -> [b]
applyAll x = map (\f -> f x)

-- | Like concat applied after mapM (or the monadic version of concatMap).
concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f x = mapM f x >>* concat

-- | Like the monadic sequence function, but for pairs instead of lists.
seqPair :: Monad m => (m a, m b) -> m (a,b)
seqPair (x,y) = do x' <- x
                   y' <- y
                   return (x',y')

-- | Finds the first element that matches the given predicate, and returns
-- (Just) it alongside the other elements of the list if it is found.  If no matching
-- element is found, Nothing is returned with the original list
findAndRemove :: (a -> Bool) -> [a] -> (Maybe a, [a])
findAndRemove _ []     = (Nothing,[])
findAndRemove f (x:xs) | f x       = (Just x,xs)
                       | otherwise = let (r,xs') = findAndRemove f xs in (r,x:xs')

-- | Forms the powerset of a given list.
-- It uses the list monad cleverly, and it scares me.  But it works.
-- Taken from: http:\/\/www.haskell.org\/haskellwiki\/Blow_your_mind
powerset :: [a] -> [[a]]
powerset = filterM (const [True, False])

-- | Alters a monadic state and returns the old value (from before the alteration).
modify' :: Monad m => (s -> s) -> StateT s m s
modify' f = do x <- get
               put (f x)
               return x

-- | Similar to modify, but the modification function is monadic, and returns a value.
modifyM :: Monad m => (s -> m (a,s)) -> StateT s m a
modifyM f = do st <- get
               (x, st') <- lift $ f st
               put st'
               return x

-- | Applies a monadic modification to the state in a StateT wrapper.
modifyM_ :: Monad m => (s -> m s) -> StateT s m ()
modifyM_ f = do st <- get
                st' <- lift $ f st
                put st'
                return ()

-- | Like lift, but instead of applying to a monadic action (m b), applies to a function (a -> m b).
liftF :: (MonadTrans t, Monad m) => (a -> m b) -> (a -> t m b)
liftF f x = lift (f x)


-- | Like the (.) operator, but for monads.
(<.<) :: Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
(<.<) f1 f0 x = f0 x >>= f1

-- | The <.< operator, flipped
(>.>) :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>.>) = flip (<.<)

-- | A size 3 version of the standard uncurry function.
uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f (x,y,z) = f x y z

-- | A size 4 version of the standard uncurry function.
uncurry4 :: (a -> b -> c -> d -> e) -> (a,b,c,d) -> e
uncurry4 f (x,y,z,a) = f x y z a

-- | Given a pair of lists, produces a list of pairs that is the cartesian product of the two lists.
product2 :: ([a],[b]) -> [(a,b)]
product2 (l0,l1) = [(x0,x1) | x0 <- l0, x1 <- l1]

-- | Given a triple of lists, produces a list of pairs that is the cartesian product of the three lists.
product3 :: ([a],[b],[c]) -> [(a,b,c)]
product3 (l0,l1,l2) = [(x0,x1,x2) | x0 <- l0, x1 <- l1, x2 <- l2]

-- | Given a quadruple of lists, produces a list of pairs that is the cartesian product of the four lists.
product4 :: ([a],[b],[c],[d]) -> [(a,b,c,d)]
product4 (l0,l1,l2,l3) = [(x0,x1,x2,x3) | x0 <- l0, x1 <- l1, x2 <- l2, x3 <- l3]

-- Given a list of lists, picks one item from each list and returns all the
-- possibilities of doing so.
--
-- So, given: [[0,1,2],[3],[],[4,5]], it should return:
-- [[0,3,4],[1,3,4],[2,3,4],[0,3,5],[1,3,5],[2,3,5]] (or some permutation thereof)
productN :: [[a]] -> [[a]]
productN [] = []
productN ([]:xss) = productN xss
productN (xs:xss) = [ y : ys | y <- xs, ys <- yss]
  where
    yss = case productN xss of
      [] -> [[]]
      z -> z

-- | Given a list, gives back the list of all permutations of the given list
--
-- Code is taken from: http://www.haskell.org/pipermail/haskell/2006-July/018298.html
-- and then fixed (missing base case, x should have been y)
permutations :: [a] -> [[a]]
permutations [] = [[]]
permutations xs = [y : ps | (y,ys) <- selections xs, ps <- permutations ys]
  where
    selections []     = []
    selections (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- selections xs]


-- | Given a list, produces all possible distinct pairings of the elements.
-- That is, for each pair returned, (A,B), B will not be the same element as A, and the pair (B,A)
-- will not be in the list.  Note that this is not the same as B /= A; if the source list contains
-- two equal items, the returned pairs will feature a pair such that B /= A.
allPairs :: [a] -> [(a,a)]
allPairs [] = []
allPairs (x:xs) = map (\y -> (x,y)) xs ++ allPairs xs

-- | On the basis of a boolean check function, transforms x into Just x if the function returns True;
-- otherwise Nothing is returned.
boolToMaybe :: (a -> Bool) -> a -> Maybe a
boolToMaybe f x = if f x then Just x else Nothing

-- | Maps over an array, but feeds the function the index too.
arrayMapWithIndex :: (IArray a e, IArray a e', Ix i) => (i -> e -> e') -> a i e -> a i e'
arrayMapWithIndex f arr = simpleArray $ map (\(i,e) -> (i,f i e)) (assocs arr)

-- | Creates an array out of an (index,value) list.  There should be no duplicate indices.
simpleArray :: (IArray a e, Ix i) => [(i,e)] -> a i e
simpleArray items = array (minimum (map fst items), maximum (map fst items)) items

-- | Zips two arrays that must have the same dimensions
arrayZipWith :: (IArray a e, IArray a e', IArray a e'', Ix i) => (e -> e' -> e'') -> a i e -> a i e' -> a i e''
arrayZipWith f a0 a1 = arrayMapWithIndex f' a0
  where
    f' i x = f x (a1 ! i)

-- | Like the (!) operator, but uses a default value when the access would be out of bounds
arrayLookupWithDefault :: (IArray a e, Ix i) => e -> a i e -> i -> e
arrayLookupWithDefault def arr ind | ind >= low && ind <= high = arr ! ind
                                   | otherwise = def
                                       where (low,high) = bounds arr

-- | Zips two arrays that can have different dimensions, using a default element
-- (for either the LHS or RHS) when needed
arrayZipWith' :: (IArray a e, Ix i) => e -> (e -> e -> e) -> a i e -> a i e -> a i e
arrayZipWith' def f a0 a1 = simpleArray $ map (\i -> (i,f' i)) allIndexes
  where
    allIndexes = nub $ indices a0 ++ indices a1

    f' i = f (arrayLookupWithDefault def a0 i) (arrayLookupWithDefault def a1 i)

-- | Zips two maps using the given function.
-- It is guaranteed that the arguments to the function will never both be Nothing; i.e. at least
-- one will be Just
zipMap :: Ord k => (Maybe v -> Maybe v' -> Maybe v'') -> Map.Map k v -> Map.Map k v' -> Map.Map k v''
zipMap f xs ys = Map.fromList $ mapMaybe f' (Set.elems allKeys)
  where
    allKeys = Map.keysSet xs `Set.union` Map.keysSet ys

    f' k = transformMaybe ((,) k) $ f (Map.lookup k xs) (Map.lookup k ys)

showMaybe :: (a -> String) -> Maybe a -> String
showMaybe showFunc (Just x) = "Just " ++ showFunc x
showMaybe _ Nothing = "Nothing"

showListCustom :: (a -> String) -> [a] -> String
showListCustom showFunc list = "[" ++ concat (intersperse "," (map showFunc list)) ++ "]"

showPairCustom :: (a -> String) -> (b -> String) -> (a,b) -> String
showPairCustom showA showB (a,b) = "(" ++ showA a ++ "," ++ showB b ++ ")"

singleton :: a -> [a]
singleton x = [x]

applyPair :: (a -> b) -> (a,a) -> (b,b)
applyPair f = transformPair f f

applyPairM :: Monad m => (a -> m b) -> (a,a) -> m (b,b)
applyPairM f = seqPair . transformPair f f

makeArraySize :: (IArray a e, Ix i, Enum i) => (i,i) -> e -> a i e -> a i e
makeArraySize size def arr = array size [(i,arrayLookupWithDefault def arr i) | i <- [fst size .. snd size]]

-- | Replace one item in a list by index.
-- This is like '(\/\/)'.
replaceAt :: Int -> a -> [a] -> [a]
replaceAt n rep es = [if i == n then rep else e | (e, i) <- zip es [0..]]

-- | A type that can contain any 'Data' item.
data DataBox = forall t. Data t => DataBox t

-- A version of mapM that acts on the values in maps.
mapMapM :: (Ord a, Monad m) => (b -> m c) -> Map.Map a b -> m (Map.Map a c)
mapMapM f m = mapMapWithKeyM (const f) m

-- A version of mapM that acts on the values in maps.
mapMapWithKeyM :: (Ord a, Monad m) => (a -> b -> m c) -> Map.Map a b -> m (Map.Map a c)
mapMapWithKeyM f m = liftM Map.fromAscList $ mapM f' $ Map.toAscList m
  where
    f' (x,y) = do y' <- f x y
                  return (x, y')

-- | Transforms an Either into a Maybe.  If it's a Left value, it is transformed
-- into Nothing.  If it is a Right value, it is transformed into Just.
eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe = either (const Nothing) Just

labelMapWithNodeId :: DynGraph gr => (Node -> a -> b) -> gr a c -> gr b c
labelMapWithNodeId f = gmap (\(x,n,l,y) -> (x,n,f n l,y))
