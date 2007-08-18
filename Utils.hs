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

-- | Given a monadic action wrapped in a Maybe, run it if there's one there;
-- if it's Nothing, then do nothing.
doMaybe :: Monad m => Maybe (m ()) -> m ()
doMaybe (Just a) = a
doMaybe Nothing = return ()

-- | Transforms between two Either types using the appropriate convert function:
transformEither :: (a -> c) -> (b -> d) -> Either a b -> Either c d
transformEither funcLeft funcRight x = case x of
  Left l -> Left (funcLeft l)
  Right r -> Right (funcRight r)
