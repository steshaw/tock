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

import Control.Monad
import Data.Ord
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

-- | Transforms between two 'Maybe' types using a function:
transformMaybe :: (a -> b) -> Maybe a -> Maybe b
transformMaybe _ Nothing = Nothing
transformMaybe f (Just x) = Just (f x)

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
