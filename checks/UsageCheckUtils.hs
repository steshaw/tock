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

module UsageCheckUtils (Decl(..), emptyVars, flattenParItems, foldUnionVars, getVarProcCall, getVarProc, labelUsageFunctions, mapUnionVars, ParItems(..), processVarW, transformParItems, UsageLabel(..), Var(..), Vars(..), vars) where

import Control.Applicative
import Control.Monad.Writer (tell)
import qualified Data.Foldable as F
import Data.Generics hiding (GT)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Traversable as T

import qualified AST as A
import CompState
import Errors
import FlowGraph
import Metadata
import OrdAST()
import ShowCode
import Types
import Utils

newtype Var = Var A.Variable
  deriving (ASTTypeable, Data, Ord, Show, ShowOccam, ShowRain, Typeable)

instance Eq Var where
  a == b = EQ == compare a b

instance ShowOccam (Set.Set Var) where
  showOccamM s
      = do tell ["{"]
           sequence $ intersperse (tell [", "]) $ map showOccamM (Set.toList s)
           tell ["}"]
instance ShowRain (Set.Set Var) where
  showRainM s
      = do tell ["{"]
           sequence $ intersperse (tell [", "]) $ map showRainM (Set.toList s)
           tell ["}"]


data Vars = Vars {
  readVars :: Set.Set Var
  ,writtenVars :: Map.Map Var (Maybe A.Expression)
  ,usedVars :: Set.Set Var -- for channels, barriers, etc
} deriving (Eq, Show)

-- | The Bool indicates whether the variable was initialised (True = yes)
data Decl = ScopeIn Bool String | ScopeOut String deriving (Show, Eq)

-- | A data type representing things that happen in parallel.
data ParItems a
  = SeqItems [a] -- ^ A list of items that happen only in sequence (i.e. none are in parallel with each other)
  | ParItems [ParItems a] -- ^ A list of items that are all in parallel with each other
  | RepParItem (A.Name, A.Replicator) (ParItems a) -- ^ A list of replicated items that happen in parallel
  deriving (Show)

data UsageLabel = Usage
  { nodeRep :: Maybe (A.Name, A.Replicator)
  , nodeDecl :: Maybe Decl
  , nodeCond :: Maybe A.Expression
  , nodeVars :: Vars
  }

instance Show UsageLabel where
  show x = "Usage (Decl{" ++ show (nodeDecl x) ++ "} Vars{" ++ show (nodeVars x) ++ "}"

transformParItems :: (a -> b) -> ParItems a -> ParItems b
transformParItems f (SeqItems xs) = SeqItems $ map f xs
transformParItems f (ParItems ps) = ParItems $ map (transformParItems f) ps
transformParItems f (RepParItem r p) = RepParItem r (transformParItems f p)

instance Functor ParItems where
  fmap = transformParItems

instance F.Foldable ParItems where
  foldr _ x (ParItems []) = x
  foldr f x (ParItems (p:ps)) = F.foldr f (F.foldr f x p) (ParItems ps)
  foldr f x (SeqItems ss) = foldr f x ss
  foldr f x (RepParItem nr p) = F.foldr f x p

instance T.Traversable ParItems where
  -- traverse :: Applicative f => (a -> f b) -> ParItems a -> f (ParItems b)
  -- <*> :: Applicative f => f (a -> b) -> f a -> f b
  traverse f (ParItems ps) = liftA ParItems $ rec ps
    where
      -- rec :: Applicative f => [ParItems a] -> f [ParItems b]
      rec [] = pure []
      rec (p:ps) = liftA2 (:) (T.traverse f p) (rec ps)
  traverse f (RepParItem nr p) = liftA (RepParItem nr) $ T.traverse f p
  traverse f (SeqItems ss) = liftA SeqItems $ rec ss
    where
      rec [] = pure []
      rec (s:ss) = liftA2 (:) (f s) (rec ss)

-- Gets all the items inside a ParItems and returns them in a flat list.
flattenParItems :: ParItems a -> [a]
flattenParItems (SeqItems xs) = xs
flattenParItems (ParItems ps) = concatMap flattenParItems ps
flattenParItems (RepParItem _ p) = flattenParItems p


emptyVars :: Vars
emptyVars = Vars Set.empty Map.empty Set.empty

mkReadVars :: [Var] -> Vars
mkReadVars ss = Vars (Set.fromList ss) Map.empty Set.empty

mkWrittenVars :: [(Var, Maybe A.Expression)] -> Vars
mkWrittenVars ss = Vars Set.empty (Map.fromList ss) Set.empty

mkUsedVars :: [Var] -> Vars
mkUsedVars vs = Vars Set.empty Map.empty (Set.fromList vs)

vars :: [Var] -> [(Var, Maybe A.Expression)] -> [Var] -> Vars
vars mr mw  u = Vars (Set.fromList mr) (Map.fromList mw) (Set.fromList u)

unionVars :: Vars -> Vars -> Vars
unionVars (Vars mr mw u) (Vars mr' mw' u') = Vars (mr `Set.union` mr') (mw `Map.union` mw') (u `Set.union` u')

foldUnionVars :: [Vars] -> Vars
foldUnionVars = foldl unionVars emptyVars

mapUnionVars :: (a -> Vars) -> [a] -> Vars
mapUnionVars f = foldUnionVars . (map f)

--Gets the (written,read) variables of a piece of an occam program:

--For subscripted variables used as Lvalues , e.g. a[b] it should return a[b] as written-to and b as read
--For subscripted variables used as expressions, e.g. a[b] it should return a[b],b as read (with no written-to)

getVarProc :: (Die m, CSMR m) => A.Process -> m Vars
getVarProc (A.Assign _ vars expList) 
        --Join together:
      = return $ unionVars
          --The written-to variables on the LHS:
          (mapUnionVars (uncurry processVarW) $ annotateVars expList vars) 
          --All variables read on the RHS:
          (getVarExpList expList)
getVarProc (A.Output _ chanVar outItems)
    = return $ (processVarUsed chanVar)
               `unionVars` (mapUnionVars getVarOutputItem outItems)
  where
    getVarOutputItem :: A.OutputItem -> Vars
    getVarOutputItem (A.OutExpression _ e) = getVarExp e
    getVarOutputItem (A.OutCounted _ ce ae) = (getVarExp ce) `unionVars` (getVarExp ae)
getVarProc (A.Input _ chanVar (A.InputSimple _ iis))
    = return $ (processVarUsed chanVar)
               `unionVars` (mapUnionVars getVarInputItem iis)
  where
    getVarInputItem :: A.InputItem -> Vars
    getVarInputItem (A.InCounted _ cv av)
        = mkWrittenVars [(variableToVar cv, Nothing), (variableToVar av, Nothing)]
    getVarInputItem (A.InVariable _ v)
        = mkWrittenVars [(variableToVar v, Nothing)]
getVarProc p@(A.ProcCall _ _ _)
    = getVarProcCall p >>* foldUnionVars
getVarProc _ = return emptyVars

getVarProcCall :: (Die m, CSMR m) => A.Process -> m [Vars]
getVarProcCall (A.ProcCall _ proc as)
    =  do st <- specTypeOfName proc
          let fs = case st of A.Proc _ _ fs _ -> fs

          sequence [getVarActual f a
                    | (f, a) <- zip fs as]

getVarActual :: (Die m, CSMR m) => A.Formal -> A.Actual -> m Vars
getVarActual _ (A.ActualExpression e) = return $ getVarExp e
getVarActual (A.Formal am t _) (A.ActualVariable v)
    = case (am, t) of
        (A.ValAbbrev,_) -> return $ processVarR v
        (_,A.Timer {}) -> return $ processVarR v
        _ -> return $ processVarW v Nothing

    {-
      Near the beginning, this piece of code was too clever for itself and applied processVarW using "everything".
      The problem with this is that given var@(A.SubscriptedVariable _ sub arrVar), the functions would be recursively
      applied to sub and arrVar.  processVarW should return var as written to, but never the subscripts in sub; those subscripts are not written to!
      
      Therefore processVarW must *not* be applied using the generics library, and instead should always be applied
      directly to an A.Variable.  Internally it uses the generics library to process the subscripts (using getVarExp)
    -}    
    
    --Pull out all the subscripts into the read category, but leave the given var in the written category:
processVarW :: A.Variable -> Maybe A.Expression -> Vars
processVarW v me = mkWrittenVars [(variableToVar v, me)]
    
processVarR :: A.Variable -> Vars
processVarR v = mkReadVars [variableToVar v]

processVarUsed :: A.Variable -> Vars
processVarUsed v = mkUsedVars [variableToVar v]

variableToVar :: A.Variable -> Var
variableToVar = Var

annotateVars :: A.ExpressionList -> [A.Variable] -> [(A.Variable, Maybe A.Expression)]
annotateVars (A.FunctionCallList {}) vs = zip vs (repeat Nothing)
annotateVars (A.IntrinsicFunctionCallList {}) vs = zip vs (repeat Nothing)
annotateVars (A.ExpressionList _ es) vs = zip vs (map Just es ++ repeat Nothing)

getVarExpList :: A.ExpressionList -> Vars
getVarExpList (A.ExpressionList _ es) = foldUnionVars $ map getVarExp es
getVarExpList (A.FunctionCallList _ _ es) = foldUnionVars $ map getVarExp es --TODO record stuff in passed as well?
getVarExpList (A.IntrinsicFunctionCallList _ _ es) = foldUnionVars $ map getVarExp es --TODO record stuff in passed as well?

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
getVarSpec (A.Specification _ n st) = get st
  where
    dv = A.Variable (A.nameMeta n) n
    
    get :: A.SpecType -> Vars
    get (A.Is _ am _ v) = abbrev am v
    get (A.IsExpr _ _ _ e) = getVarExp e `unionVars` processVarW dv (Just e)
    get (A.IsChannelArray _ _ vs) = vars vs' ((Var dv,Nothing):(zip vs' $ repeat Nothing)) []
      where
        vs' = map Var vs
    get (A.Retypes _ am _ v) = abbrev am v
    get (A.RetypesExpr _ _ _ e) = getVarExp e `unionVars` processVarW dv (Just e)
    get _ = emptyVars

    abbrev :: A.AbbrevMode -> A.Variable -> Vars
    abbrev A.Abbrev v = vars [Var v] [(Var v, Nothing), (Var dv, Just $ A.ExprVariable (findMeta v) v)] []
    abbrev _ v = processVarR v `unionVars` processVarW dv
      (Just $ A.ExprVariable (findMeta v) v)

getDecl :: (String -> Decl) -> A.Specification -> Maybe Decl
getDecl f (A.Specification _ name _) = Just $ f (A.nameName name)

getVarFormals :: Meta -> [A.Formal] -> Vars
getVarFormals m = mapUnionVars (getVarFormal m)
  where
    -- We treat formal parameters as being written-to, so that they
    -- appear initialised at the beginning of the function
    getVarFormal :: Meta -> A.Formal -> Vars
    getVarFormal m (A.Formal _ _ n) = processVarW (A.Variable m n) Nothing

getVarRepExp :: A.Replicator -> Vars
getVarRepExp (A.For _ e0 e1 e2) = getVarExp e0 `unionVars` getVarExp e1 `unionVars`
  getVarExp e2
getVarRepExp (A.ForEach _ e) = getVarExp e

getVarAlternative :: A.Alternative -> Vars
getVarAlternative = const emptyVars -- TODO

labelUsageFunctions :: forall m. (Die m, CSMR m) => GraphLabelFuncs m UsageLabel
labelUsageFunctions = GLF
 {
   labelExpression = single getVarExp
  ,labelConditionalExpression
    = \e -> return $ Usage Nothing Nothing (Just e) (getVarExp e)
  ,labelExpressionList = single getVarExpList
  ,labelDummy = const (return $ Usage Nothing Nothing Nothing emptyVars)
  ,labelProcess = singleM getVarProc
  ,labelAlternative = single getVarAlternative
  ,labelStartNode = single (uncurry getVarFormals)
  ,labelReplicator = \x -> return (Usage (Just x) Nothing Nothing (getVarRepExp $ snd x))
  --don't forget about the variables used as initialisers in declarations (hence getVarSpec)
  ,labelScopeIn = pair (getDecl $ ScopeIn False) getVarSpec
  ,labelScopeOut = pair (getDecl ScopeOut) (const emptyVars)
 }
  where
    single :: (a -> Vars) -> (a -> m UsageLabel)
    single f x = return $ Usage Nothing Nothing Nothing (f x)

    singleM :: (a -> m Vars) -> (a -> m UsageLabel)
    singleM f x = f x >>* Usage Nothing Nothing Nothing

    pair :: (a -> Maybe Decl) -> (a -> Vars) -> (a -> m UsageLabel)
    pair f0 f1 x = return $ Usage Nothing (f0 x) Nothing (f1 x)
