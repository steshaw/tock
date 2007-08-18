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

-- | A generic show implementation that pretty-prints expressions.
-- This ought to use a class (like show does), so that it can be extended
-- properly without me needing to have Tock-specific cases in here -- see the
-- appropriate SYB paper.
module PrettyShow (pshow, isTupleCtr) where

import Data.Generics
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ

import qualified AST as A
import Metadata

-- This is ugly -- but it looks like you can't easily define a generic function
-- even for a single tuple type, since it has to parameterise over multiple Data
-- types...
isTupleCtr :: String -> Bool
isTupleCtr ('(':cs) = checkRest cs
  where
    checkRest ",)" = True
    checkRest (',':cs) = checkRest cs
    checkRest _ = False
isTupleCtr _ = False

doGeneral :: Data a => a -> Doc
doGeneral t =
  if isTupleCtr cn then
    parens $ sep $ punctuate (text ",") l
  else case l of
    [] -> con
    otherwise -> parens $ sep (con : l)
  where
    cn = showConstr (toConstr t)
    con = text $ cn
    l = gmapQ doAny t

doList :: Data a => [a] -> Doc
doList t = brackets $ sep $ punctuate (text ",") (map doAny t)

doString :: String -> Doc
doString s = text $ show s

doMeta :: Meta -> Doc
doMeta m = text $ show m

doMap :: (Data a, Data b) => Map.Map a b -> Doc
doMap map = braces $ sep $ punctuate (text ",") [doAny k <+> text ":" <+> doAny v
                                                 | (k, v) <- Map.toAscList map]

doAny :: Data a => a -> Doc
doAny = doGeneral `ext1Q` doList `extQ` doString `extQ` doMeta
          `extQ` (doMap :: Map.Map String String -> Doc)
          `extQ` (doMap :: Map.Map String A.NameDef -> Doc)
          `extQ` (doMap :: Map.Map String [A.Type] -> Doc)
          `extQ` (doMap :: Map.Map String [A.Actual] -> Doc)

-- | Convert an arbitrary data structure to a string in a reasonably pretty way.
-- This is currently rather slow.
pshow :: Data a => a -> String
pshow x = render $ doAny x

