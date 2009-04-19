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

-- | Analyse syntactic structure of occam code.
module StructureOccam (structureOccam) where

import Errors
import LexOccam
import Metadata
import Pass

-- | Reserved words that, if found at the end of a line, indicate the next
-- line is a continuation.
continuationWords :: [String]
continuationWords
  = [ "-", "~", "+", "-", "*", "/", "\\", "/\\", "\\/", "><", "=", "<>",
      "<", ">", ">=", "<=", ",", ";", ":=", "<<", ">>",
      "AFTER", "AND", "BITAND", "BITNOT", "BITOR", "FOR", "FROM",
      "IS", "MINUS", "MINUS", "NOT", "OR", "PLUS", "REM", "RESHAPES",
      "RETYPES", "SIZE", "TIMES" ]

-- | Given the output of the lexer for a single file, add `Indent`, `Outdent`
-- and `EndOfLine` markers.
structureOccam :: forall m. Die m => [Token] -> m [Token]
structureOccam [] = return []
structureOccam ts = analyse 1 firstLine ts (Token emptyMeta EndOfLine)
  where
    -- Find the first line that's actually got something on it.
    firstLine
        = case ts of ((Token m _):_) -> metaLine m

    analyse :: Int -> Int -> [Token] -> Token -> m [Token]
    -- Add extra EndOfLine at the end of the file.
    analyse prevCol _ [] _ = return $ Token emptyMeta EndOfLine : out
      where out = replicate (prevCol `div` 2) (Token emptyMeta Outdent)
    analyse prevCol prevLine (t@(Token m tokType):ts) prevTok
      | line /= prevLine && not isContinuation
        = do rest <- analyse col line ts t
             newLine $ t : rest
      | otherwise
        = do rest <- analyse prevCol line ts t
             return $ t : rest
      where
        col = metaColumn m
        line = metaLine m

        isContinuation = case prevTok of
                           Token _ (TokReserved s) ->
                             s `elem` continuationWords
                           Token _ (TokStringCont _) -> True
                           _ -> False

        -- A new line -- look to see what's going on with the indentation.
        newLine :: [Token] -> m [Token]
        newLine rest
          | col == prevCol + 2   = withEOL $ Token m Indent : rest
          -- FIXME: If col > prevCol, then look to see if there's a VALOF
          -- coming up before the next column change...
          | col < prevCol
              = if (prevCol - col) `mod` 2 == 0
                  then withEOL $ replicate steps (Token m Outdent) ++ rest
                  else bad
          | col == prevCol       = withEOL rest
          | otherwise            = bad
            where
              steps = (prevCol - col) `div` 2
              bad :: m [Token]
              bad = dieP m "Invalid indentation"
              -- This is actually the position at which the new line starts
              -- rather than the end of the previous line.
              withEOL ts = return $ Token m EndOfLine : ts

