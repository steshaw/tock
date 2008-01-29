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

module UsageCheckUtils (customVarCompare, Decl(..), emptyVars, foldUnionVars, getVarActual, getVarProc, labelFunctions, mapUnionVars, ParItems(..), processVarW, transformParItems, Var(..), Vars(..), vars) where

import Data.Generics hiding (GT)
import Data.List
import Data.Maybe
import qualified Data.Set as Set

import qualified AST as A
import Errors
import FlowGraph
import OrdAST()
import ShowCode

newtype Var = Var A.Variable deriving (Data, Show, Typeable)


customVarCompare :: A.Variable -> A.Variable -> Ordering
customVarCompare (A.Variable _ (A.Name _ _ lname)) (A.Variable _ (A.Name _ _ rname)) = compare lname rname
customVarCompare (A.Variable {}) _ = LT
-- TODO the rest (will need an ordering over Expression, yikes!)
--customVarCompare _ _ = GT

instance Eq Var where
  a == b = EQ == compare a b

instance Ord Var where
  compare (Var a) (Var b) = compare a b

instance ShowOccam Var where
  showOccamM (Var v) = showOccamM v
instance ShowRain Var where
  showRain (Var v) = showRain v

instance ShowOccam (Set.Set Var) where
  showOccamM s
      = do ss <- mapM showOccamM (Set.toList s)
           return $ "{" ++ concat (intersperse ", " ss) ++ "}"
instance ShowRain (Set.Set Var) where
  showRain s = "{" ++ concat (intersperse ", " $ map showRain $ Set.toList s) ++ "}"

data Vars = Vars {
  readVars :: Set.Set Var
  ,writtenVars :: Set.Set Var
  ,usedVars :: Set.Set Var -- for channels, barriers, etc
} deriving (Eq, Show)

data Decl = ScopeIn String | ScopeOut String deriving (Show, Eq)

-- | A data type representing things that happen in parallel.
data ParItems a
  = SeqItems [a] -- ^ A list of items that happen only in sequence (i.e. none are in parallel with each other)
  | ParItems [ParItems a] -- ^ A list of items that are all in parallel with each other
  | RepParItem A.Replicator (ParItems a) -- ^ A list of replicated items that happen in parallel

transformParItems :: (a -> b) -> ParItems a -> ParItems b
transformParItems f (SeqItems xs) = SeqItems $ map f xs
transformParItems f (ParItems ps) = ParItems $ map (transformParItems f) ps
transformParItems f (RepParItem r p) = RepParItem r (transformParItems f p)

emptyVars :: Vars
emptyVars = Vars Set.empty Set.empty Set.empty

mkReadVars :: [Var] -> Vars
mkReadVars ss = Vars (Set.fromList ss) Set.empty Set.empty

mkWrittenVars :: [Var] -> Vars
mkWrittenVars ss = Vars Set.empty (Set.fromList ss) Set.empty

mkUsedVars :: [Var] -> Vars
mkUsedVars vs = Vars Set.empty Set.empty (Set.fromList vs)

vars :: [Var] -> [Var] -> [Var] -> Vars
vars mr mw  u = Vars (Set.fromList mr) (Set.fromList mw) (Set.fromList u)

unionVars :: Vars -> Vars -> Vars
unionVars (Vars mr mw u) (Vars mr' mw' u') = Vars (mr `Set.union` mr') (mw `Set.union` mw') (u `Set.union` u')

foldUnionVars :: [Vars] -> Vars
foldUnionVars = foldl unionVars emptyVars

mapUnionVars :: (a -> Vars) -> [a] -> Vars
mapUnionVars f = foldUnionVars . (map f)

--Gets the (written,read) variables of a piece of an occam program:

--For subscripted variables used as Lvalues , e.g. a[b] it should return a[b] as written-to and b as read
--For subscripted variables used as expressions, e.g. a[b] it should return a[b],b as read (with no written-to)

getVarProc :: A.Process -> Vars
getVarProc (A.Assign _ vars expList) 
        --Join together:
      = unionVars
          --The written-to variables on the LHS:
          (mapUnionVars processVarW vars) 
          --All variables read on the RHS:
          (getVarExpList expList)
getVarProc (A.GetTime _ v) = processVarW v
getVarProc (A.Wait _ _ e) = getVarExp e
getVarProc (A.Output _ chanVar outItems) = (processVarUsed chanVar) `unionVars` (mapUnionVars getVarOutputItem outItems)
  where
    getVarOutputItem :: A.OutputItem -> Vars
    getVarOutputItem (A.OutExpression _ e) = getVarExp e
    getVarOutputItem (A.OutCounted _ ce ae) = (getVarExp ce) `unionVars` (getVarExp ae)
getVarProc (A.Input _ chanVar (A.InputSimple _ iis)) = (processVarUsed chanVar) `unionVars` (mapUnionVars getVarInputItem iis)
  where
    getVarInputItem :: A.InputItem -> Vars
    getVarInputItem (A.InCounted _ cv av) = mkWrittenVars [variableToVar cv,variableToVar av]
    getVarInputItem (A.InVariable _ v) = mkWrittenVars [variableToVar v]
getVarProc (A.ProcCall _ _ params) =  mapUnionVars getVarActual params
getVarProc _ = emptyVars

getVarActual :: A.Actual -> Vars
getVarActual (A.ActualExpression _ e) = getVarExp e
getVarActual (A.ActualVariable A.ValAbbrev _ v) = processVarR v
getVarActual (A.ActualVariable _ _ v) = processVarW v

    {-
      Near the beginning, this piece of code was too clever for itself and applied processVarW using "everything".
      The problem with this is that given var@(A.SubscriptedVariable _ sub arrVar), the functions would be recursively
      applied to sub and arrVar.  processVarW should return var as written to, but never the subscripts in sub; those subscripts are not written to!
      
      Therefore processVarW must *not* be applied using the generics library, and instead should always be applied
      directly to an A.Variable.  Internally it uses the generics library to process the subscripts (using getVarExp)
    -}    
    
    --Pull out all the subscripts into the read category, but leave the given var in the written category:
processVarW :: A.Variable -> Vars
processVarW v = mkWrittenVars [variableToVar v]
    
processVarR :: A.Variable -> Vars
processVarR v = mkReadVars [variableToVar v]

processVarUsed :: A.Variable -> Vars
processVarUsed v = mkUsedVars [variableToVar v]

variableToVar :: A.Variable -> Var
variableToVar = Var

getVarExpList :: A.ExpressionList -> Vars
getVarExpList (A.ExpressionList _ es) = foldUnionVars $ map getVarExp es
getVarExpList (A.FunctionCallList _ _ es) = foldUnionVars $ map getVarExp es --TODO record stuff in passed as well?

getVarExp :: A.Expression -> Vars
getVarExp = everything unionVars (emptyVars `mkQ` getVarExp')
  where
    --Only need to deal with the two cases where we can see an A.Variable directly;
    --the generic recursion will take care of nested expressions, and even the expressions used as subscripts
    getVarExp' :: A.Expression -> Vars
    getVarExp' (A.SizeVariable _ v) = processVarR v
    getVarExp' (A.ExprVariable _ v) = processVarR v
    getVarExp' _ = emptyVars

getVarSpec :: A.Specification -> Vars
getVarSpec = const emptyVars -- TODO

getDecl :: (String -> Decl) -> A.Specification -> Maybe Decl
getDecl _ _ = Nothing -- TODO


labelFunctions :: forall m. Die m => GraphLabelFuncs m (Maybe Decl, Vars)
labelFunctions = GLF
 {
   labelExpression = pair (const Nothing) getVarExp
  ,labelExpressionList = pair (const Nothing) getVarExpList
  ,labelDummy = const (return (Nothing, emptyVars))
  ,labelProcess = pair (const Nothing) getVarProc
  --don't forget about the variables used as initialisers in declarations (hence getVarSpec)
  ,labelScopeIn = pair (getDecl ScopeIn) getVarSpec
  ,labelScopeOut = pair (getDecl ScopeOut) (const emptyVars)
 }
  where
    pair :: (a -> b) -> (a -> c) -> (a -> m (b,c))
    pair f0 f1 x = return (f0 x, f1 x)
