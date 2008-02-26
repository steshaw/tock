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

-- | Metadata -- i.e. source position.
module Metadata where

{-! global : Haskell2Xml !-}

import Data.Generics
import Text.Printf
import Text.Read

data Meta = Meta {
    metaFile :: Maybe String,
    metaLine :: Int,
    metaColumn :: Int
  }
  deriving (Typeable, Data, Ord, Eq)

emptyMeta :: Meta
emptyMeta = Meta {
              metaFile = Nothing,
              metaLine = 0,
              metaColumn = 0
            }

instance Show Meta where
  show m =
      case metaFile m of
        Just s -> s ++ ":" ++ show (metaLine m) ++ ":" ++ show (metaColumn m)
        Nothing -> "no source position"

-- | Encode a Meta as the prefix of a string.
packMeta :: Meta -> String -> String
packMeta m s
    = case metaFile m of
        Nothing -> s
        Just fn -> printf "~%d\0%d\0%s\0%s"
                          (metaLine m) (metaColumn m) fn s

-- | Extract a Meta (encoded by packMeta) from a String.
unpackMeta :: String -> (Maybe Meta, String)
unpackMeta ('~':s) = (Just m, rest)
  where
    (ls, _:s') = break (== '\0') s
    (cs, _:s'') = break (== '\0') s'
    (fn, _:rest) = break (== '\0') s''
    m = emptyMeta {
          metaFile = Just fn,
          metaLine = read ls,
          metaColumn = read cs
        }
unpackMeta s = (Nothing, s)

-- | Find the first Meta value in some part of the AST.
findMeta :: (Data t, Typeable t) => t -> Meta
findMeta e = case cast e of
               Just m -> m
               Nothing -> if null (concat metaList) then emptyMeta else head (concat metaList)
  where
    metaList = gmapQ (mkQ [] findMeta') e
    findMeta' :: Meta -> [Meta]
    findMeta' m = [m]
