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

module ParseUtils where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos (newPos)
import Metadata

--{{{ Meta to/from SourcePos
-- | Convert source position into Parsec's format.
metaToSourcePos :: Meta -> SourcePos
metaToSourcePos meta
    = newPos filename (metaLine meta) (metaColumn meta)
  where
    filename = case metaFile meta of
                 Just s -> s
                 Nothing -> ""

-- | Convert source position out of Parsec's format.
sourcePosToMeta :: SourcePos -> Meta
sourcePosToMeta pos
    = emptyMeta {
        metaFile = case sourceName pos of
                     "" -> Nothing
                     s -> Just s,
        metaLine = sourceLine pos,
        metaColumn = sourceColumn pos
      }
--}}}


