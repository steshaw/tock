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
module PrettyShow (pshow, pshowCode) where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import qualified AST as A
import CompState
import Metadata
import Pattern
import ShowCode

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

doGeneral :: Data a => GenericQ Doc -> a -> Doc
doGeneral anyFunc t =
  if isTupleCtr cn then
    parens $ sep $ punctuate (text ",") l
  else case l of
    [] -> con
    otherwise -> parens $ sep (con : l)
  where
    cn = showConstr (toConstr t)
    con = text $ cn
    l = gmapQ anyFunc t

doList :: Data a => GenericQ Doc -> [a] -> Doc
doList anyFunc t = brackets $ sep $ punctuate (text ",") (map anyFunc t)

doString :: String -> Doc
doString s = text $ show s

doMeta :: Meta -> Doc
doMeta m = text $ show m

doMap :: (Data a, Data b) => GenericQ Doc -> Map.Map a b -> Doc
doMap anyFunc map = braces $ sep $ punctuate (text ",") [anyFunc k <+> text ":" <+> anyFunc v
                                                         | (k, v) <- Map.toAscList map]

doSet :: Data a => GenericQ Doc -> Set.Set a -> Doc
doSet anyFunc set = brackets $ sep $ punctuate (text ",") (map anyFunc $ Set.toList set)

foldPatternList :: Pattern -> [Pattern]
foldPatternList (Match con patList)
  = if (showConstr con == "(:)")
    then
      --patList must contain two items.  The first is the list item (to be returned), the second is a nested list -- possibly the empty list
      (head patList) : (foldPatternList $ last patList)
    else []
foldPatternList _ = []

showStringPattern :: [Pattern] -> String
showStringPattern = concatMap showCharPattern
  where
    showCharPattern :: Pattern -> String
    showCharPattern (Match c _) = show c
    showCharPattern _ = ""

--Checks whether every item in a pattern list is (effectively) a Char
wholeString :: [Pattern] -> Bool
wholeString ((Match con []):ps)
  = case (constrRep con) of
      StringConstr _ -> True && (wholeString ps)
      _ -> False
wholeString (_:_) = False
wholeString [] = True

                                                 
--Print the data nicely for Pattern.Pattern, to make it look like a pattern match:
doPattern :: Pattern -> Doc
doPattern (DontCare) = text "_"
doPattern (Named s p) = (text (s ++ "@")) <> (doPattern p)
doPattern p@(Match c ps) =
  --All a bit hacky, admittedly:
 if isTupleCtr (showConstr c)
 --It's a tuple:
 then parens $ sep $ punctuate (text ",") items
 else
     if (showConstr c == "(:)")
     --It's a list:
     then
       if (wholeString folded)
           --It's a string:
       then doString (showStringPattern folded)
           --It's some other kind of list:
       else doList (mkQ empty doPattern) folded
     --It's neither a list nor a tuple:
     else parens $ (text (showConstr c)) $+$ (sep items)
   where
     items = map doPattern ps
     folded = foldPatternList p

doAny :: (forall a. Typeable a => (a -> Doc) -> (a -> Doc)) -> GenericQ Doc
doAny extFunc = extFunc (
  (doGeneral anyFunc) `ext1Q` (doList anyFunc) `extQ` doString `extQ` doMeta `extQ` doPattern
          `extQ` (doMap anyFunc :: Map.Map String String -> Doc)
          `extQ` (doMap anyFunc :: Map.Map String A.NameDef -> Doc)
          `extQ` (doMap anyFunc :: Map.Map String [A.Type] -> Doc)
          `extQ` (doMap anyFunc :: Map.Map String [A.Actual] -> Doc)
          `extQ` (doSet anyFunc :: Set.Set String -> Doc)
          `extQ` (doSet anyFunc :: Set.Set A.Name -> Doc)
  )
     where
       anyFunc :: GenericQ Doc
       anyFunc = doAny extFunc

-- | Convert an arbitrary data structure to a string in a reasonably pretty way.
-- This is currently rather slow.
pshow :: Data a => a -> String
pshow x = render $ doAny id x

pshowCode :: (Data a, CSM m) => a -> m String
pshowCode c = do st <- get
                 case csFrontend st of
                   FrontendOccam -> return $ render $ (extOccam $ doAny extOccam) c
                   FrontendRain -> return $ render $ (extRain $ doAny extRain) c
  where
    extOccam :: forall a. Typeable a => (a -> Doc) -> (a -> Doc)
    extOccam f = extCode f showOccam
    extRain :: forall a. Typeable a => (a -> Doc) -> (a -> Doc)
    extRain f = extCode f showRain
