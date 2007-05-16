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

