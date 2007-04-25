-- | Parse indentation in occam source.
module Indentation (parseIndentation, indentMarker, outdentMarker, eolMarker) where

import Data.List

-- FIXME this doesn't handle multi-line strings
-- FIXME or VALOF processes
-- FIXME or continuation lines...

indentMarker = "__indent"
outdentMarker = "__outdent"
eolMarker = "__eol"

countIndent :: String -> Int -> Int
-- Tabs are 8 spaces.
countIndent ('\t':cs) lineNum = 4 + (countIndent cs lineNum)
countIndent (' ':' ':cs) lineNum = 1 + (countIndent cs lineNum)
countIndent (' ':cs) lineNum = error $ "Bad indentation at line " ++ show lineNum
countIndent _ _ = 0

stripIndent :: String -> String
stripIndent (' ':cs) = stripIndent cs
stripIndent cs = cs

stripComment :: String -> Int -> String
stripComment [] _ = []
stripComment ('-':'-':s) _ = []
stripComment ('"':s) lineNum = '"' : stripCommentInString s lineNum
stripComment (c:s) lineNum = c : stripComment s lineNum

stripCommentInString :: String -> Int -> String
stripCommentInString [] lineNum = error $ "In string at end of line " ++ show lineNum
stripCommentInString ('"':s) lineNum = '"' : stripComment s lineNum
stripCommentInString (c:s) lineNum = c : stripCommentInString s lineNum

parseIndentation :: [String] -> String
parseIndentation ls = concat $ intersperse "\n" $ lines
  where
    (initSuffix, lines) = flatten' ls 0 1
    rep n i = concat $ take n (repeat i)
    flatten' [] level lineNum = ("", [rep level (' ' : outdentMarker)])
    flatten' (s:ss) level lineNum
      | isBlankLine      = let (suffix, rest) = flatten' ss level (lineNum + 1) in (suffix, "" : rest)
      | newLevel > level = (rep (newLevel - level) (' ' : indentMarker), processed : rest)
      | newLevel < level = (rep (level - newLevel) (' ' : outdentMarker), processed : rest)
      | otherwise        = ("", processed : rest)
      where newLevel = countIndent s lineNum
            stripped' = stripComment s lineNum
            isBlankLine = stripIndent stripped' == ""
            processed = (if isBlankLine then "" else (stripped' ++ (' ' : eolMarker))) ++ suffix
            (suffix, rest) = flatten' ss newLevel (lineNum + 1)

