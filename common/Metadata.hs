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

import Data.Generics

import Utils

data Meta = Meta {
    metaFile :: Maybe String,
    metaLine :: Int,
    metaColumn :: Int
  }
  deriving (Typeable, Data)

emptyMeta :: Meta
emptyMeta = Meta {
              metaFile = Nothing,
              metaLine = 0,
              metaColumn = 0
            }

instance Show Meta where
  show m =
      case metaFile m of
        Just s -> basenamePath s ++ ":" ++ show (metaLine m) ++ ":" ++ show (metaColumn m)
        Nothing -> "no source position"

--emptyMeta is equal to any meta tag:
instance Eq Meta where
  (==) a b = 
    if ((metaFile a == Nothing) && (metaLine a == 0) && (metaColumn a == 0)) then True else
    if ((metaFile b == Nothing) && (metaLine b == 0) && (metaColumn b == 0)) then True else
    ((metaFile a == metaFile b) && (metaLine a == metaLine b) && (metaColumn a == metaColumn b))