{-
Tock: a compiler for parallel languages
Copyright (C) 2009  University of Kent

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

module Operators where

import Data.Char

isOperator :: String -> Bool
isOperator op = any (== op) operatorNames

operatorNames :: [String]
operatorNames =
  ["??"
  ,"@@"
  ,"$$"
  ,"%"
  ,"%%"
  ,"&&"
  ,"<%"
  ,"%>"
  ,"<&"
  ,"&>"
  ,"<]"
  ,"[>"
  ,"<@"
  ,"@>"
  ,"@"
  ,"++"
  ,"!!"
  ,"=="
  ,"^"
  ,"-"
  ,"MINUS"
  ,"~"
  ,"NOT"
  ,"+"
  ,"*"
  ,"/"
  ,"\\"
  ,"REM"
  ,"PLUS"
  ,"TIMES"
  ,"AFTER"
  ,"/\\"
  ,"\\/"
  ,"><"
  ,"BITNOT"
  ,"BITAND"
  ,"BITOR"
  ,"<<"
  ,">>"
  ,"AND"
  ,"OR"
  ,"="
  ,"<>"
  ,"<="
  ,"<"
  ,">="
  ,">"
  ]

-- | This gives a default mapping from operator (such as "+") to a valid name string
-- to be used in the backend (i.e. the Tock support headers), such as "add", which
-- will later be suffixed by the types in question.
occamOperatorTranslateDefault :: String -> String
occamOperatorTranslateDefault "+" = "add"
occamOperatorTranslateDefault "-" = "subtr"
occamOperatorTranslateDefault "*" = "mul"
occamOperatorTranslateDefault "/" = "div"
occamOperatorTranslateDefault "TIMES" = "times"
occamOperatorTranslateDefault "PLUS" = "plus"
occamOperatorTranslateDefault "MINUS" = "minus"
occamOperatorTranslateDefault "AFTER" = "after"
occamOperatorTranslateDefault ">" = "more"
occamOperatorTranslateDefault "<" = "less"
occamOperatorTranslateDefault ">=" = "moreEq"
occamOperatorTranslateDefault "<=" = "lessEq"
occamOperatorTranslateDefault "=" = "eq"
occamOperatorTranslateDefault "<>" = "notEq"
occamOperatorTranslateDefault "\\" = "rem"
occamOperatorTranslateDefault "REM" = "REM"
occamOperatorTranslateDefault "/\\" = "and"
occamOperatorTranslateDefault "\\/" = "or"
occamOperatorTranslateDefault "><" = "xor"
occamOperatorTranslateDefault "<<" = "lshift"
occamOperatorTranslateDefault ">>" = "rshift"
occamOperatorTranslateDefault "AND" = "and"
occamOperatorTranslateDefault "OR" = "or"
occamOperatorTranslateDefault "NOT" = "not"
occamOperatorTranslateDefault "~" = "not"
occamOperatorTranslateDefault cs = "op_" ++ concatMap (show . ord) cs

