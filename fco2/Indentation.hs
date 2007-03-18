module Indentation (parseIndentation, indentMarker, outdentMarker, eolMarker) where

import Data.List

-- XXX this doesn't handle multi-line strings
-- XXX or VALOF processes
-- XXX or tabs

indentMarker = "__indent"
outdentMarker = "__outdent"
eolMarker = "__eol"

countIndent :: String -> Int
countIndent (' ':' ':cs) = 1 + (countIndent cs)
countIndent (' ':cs) = error "Bad indentation"
countIndent _ = 0

stripIndent :: String -> String
stripIndent (' ':cs) = stripIndent cs
stripIndent cs = cs

stripComment :: String -> String
stripComment [] = []
stripComment ('-':'-':s) = []
stripComment ('"':s) = '"' : stripCommentInString s
stripComment (c:s) = c : stripComment s

stripCommentInString :: String -> String
stripCommentInString [] = error "In string at end of line"
stripCommentInString ('"':s) = '"' : stripComment s
stripCommentInString (c:s) = c : stripCommentInString s

parseIndentation :: [String] -> String
parseIndentation ls = concat $ intersperse "\n" $ lines
  where
    (initSuffix, lines) = flatten' ls 0
    rep n i = concat $ take n (repeat i)
    flatten' [] level = ("", [rep level (' ' : outdentMarker)])
    flatten' (s:ss) level
      | stripped == ""   = let (suffix, rest) = flatten' ss level in ("", suffix : rest)
      | newLevel > level = (rep (newLevel - level) (' ' : indentMarker), stripped : rest)
      | newLevel < level = (rep (level - newLevel) (' ' : outdentMarker), stripped : rest)
      | otherwise        = ("", stripped : rest)
      where newLevel = countIndent s
            stripped' = stripComment s
            stripped = (if stripIndent stripped' == "" then "" else (stripped' ++ (' ' : eolMarker))) ++ suffix
            (suffix, rest) = flatten' ss newLevel

