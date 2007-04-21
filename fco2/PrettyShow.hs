-- | A generic show implementation that pretty-prints expressions.
-- This ought to use a class (like show does), so that it can be extended
-- properly without me needing to have FCO-specific cases in here -- see the
-- appropriate SYB paper.
module PrettyShow (pshow) where

import Data.Generics
import Text.PrettyPrint.HughesPJ
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

doAny :: Data a => a -> Doc
doAny = doGeneral `ext1Q` doList `extQ` doString `extQ` doMeta

-- | Convert an arbitrary data structure to a string in a reasonably pretty way.
-- This is currently rather slow.
pshow :: Data a => a -> String
pshow x = render $ doAny x

