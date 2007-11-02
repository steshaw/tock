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

-- | This code implements the usage checking in Rain.  It is designed to work with
-- the control-flow graph stuff, hence the use of functions that match the dictionary
-- of functions in FlowGraph.  This is also why we don't drill down into processes;
-- the control-flow graph means that we only need to concentrate on each node that isn't nested.
module RainUsageCheck where

import Control.Monad.Error
import Control.Monad.Identity
import Data.Generics
import Data.Graph.Inductive
import Data.List hiding (union)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import qualified AST as A
import FlowAlgorithms
import FlowGraph

-- In Rain, Deref can't nest with Dir in either way, so this doesn't need to be a recursive type:
data Var =
  Plain String
  | Deref String
  | Dir A.Direction String
  deriving (Eq, Show, Ord)
  
data Vars = Vars {
  maybeRead :: Set.Set Var,
  maybeWritten :: Set.Set Var,
  defWritten :: Set.Set Var,
  used :: Set.Set Var -- e.g. channels, barriers
--  passed :: Set.Set String
}
  deriving (Eq, Show)

emptyVars :: Vars
emptyVars = Vars Set.empty Set.empty Set.empty Set.empty

readVars :: [Var] -> Vars
readVars ss = Vars (Set.fromList ss) Set.empty Set.empty Set.empty

writtenVars :: [Var] -> Vars
writtenVars ss = Vars Set.empty (Set.fromList ss) (Set.fromList ss) Set.empty

usedVars :: [Var] -> Vars
usedVars vs = Vars Set.empty Set.empty Set.empty (Set.fromList vs)

vars :: [Var] -> [Var] -> [Var] -> [Var] -> Vars
vars mr mw dw u = Vars (Set.fromList mr) (Set.fromList mw) (Set.fromList dw) (Set.fromList u)

unionVars :: Vars -> Vars -> Vars
unionVars (Vars mr mw dw u) (Vars mr' mw' dw' u') = Vars (mr `Set.union` mr') (mw `Set.union` mw') (dw `Set.union` dw') (u `Set.union` u')

foldUnionVars :: [Vars] -> Vars
foldUnionVars = foldl unionVars emptyVars

mapUnionVars :: (a -> Vars) -> [a] -> Vars
mapUnionVars f = foldUnionVars . (map f)

nameToString :: A.Name -> String
nameToString = A.nameName

--Gets the (written,read) variables of a piece of an occam program:

--For subscripted variables used as Lvalues , e.g. a[b] it should return a[b] as written-to and b as read
--For subscripted variables used as expressions, e.g. a[b] it should return a[b],b as read (with no written-to)

getVarProc :: A.Process -> Vars
getVarProc (A.Assign _ vars expList) 
        --Join together:
      = unionVars
          --The written-to variables on the LHS:
          (foldUnionVars (map processVarW vars)) 
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
    getVarInputItem (A.InCounted _ cv av) = writtenVars [variableToVar cv,variableToVar av]
    getVarInputItem (A.InVariable _ v) = writtenVars [variableToVar v]
--TODO process calls
getVarProc _ = emptyVars
    
    {-
      Near the beginning, this piece of code was too clever for itself and applied processVarW using "everything".
      The problem with this is that given var@(A.SubscriptedVariable _ sub arrVar), the functions would be recursively
      applied to sub and arrVar.  processVarW should return var as written to, but never the subscripts in sub; those subscripts are not written to!
      
      Therefore processVarW must *not* be applied using the generics library, and instead should always be applied
      directly to an A.Variable.  Internally it uses the generics library to process the subscripts (using getVarExp)
    -}    
    
    --Pull out all the subscripts into the read category, but leave the given var in the written category:
processVarW :: A.Variable -> Vars
processVarW v = writtenVars [variableToVar v]
    
processVarR :: A.Variable -> Vars
processVarR v = readVars [variableToVar v]

processVarUsed :: A.Variable -> Vars
processVarUsed v = usedVars [variableToVar v]

variableToVar :: A.Variable -> Var
variableToVar (A.Variable _ n) = Plain $ nameToString n
variableToVar (A.DirectedVariable _ dir (A.Variable _ n)) = Dir dir $ nameToString n
variableToVar (A.DerefVariable _ (A.Variable _ n)) = Deref $ nameToString n
variableToVar v = error ("Unprocessable variable: " ++ show v) --TODO come up with a better solution than this

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

data Decl = ScopeIn String | ScopeOut String deriving (Show, Eq)

getDecl :: (String -> Decl) -> A.Specification -> Maybe Decl
getDecl _ _ = Nothing -- TODO


getVarLabelFuncs :: GraphLabelFuncs Identity (Maybe Decl, Vars)
getVarLabelFuncs = GLF
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
    pair :: (a -> b) -> (a -> c) -> (a -> Identity (b,c))
    pair f0 f1 x = return (f0 x, f1 x)

{-


-- I am not sure how you could build this out of the standard functions, so I built it myself
--Takes a list (let's say Y), a function that applies to a single item and a list, and then goes through applying the function
--to each item in the list, with the rest of the list Y as a parameter.  Perhaps the code is clearer:
permuteHelper :: (a -> [a] -> b) -> [a] -> [b]
permuteHelper _ [] = []
permuteHelper func (x:xs) = permuteHelper' func [] x xs
  where
    permuteHelper' :: (a -> [a] -> b) -> [a] -> a -> [a] -> [b]
    permuteHelper' func prev cur [] = [func cur prev]
    permuteHelper' func prev cur (next:rest) = (func cur (prev ++ (next:rest))) : (permuteHelper' func (prev ++ [cur]) next rest)


--Whereas the other passes (at the current time of writing) are transforms on the tree, the usage checker
--does not modify the tree at all; it only needs to check if the usage is valid or not.  Therefore instead
--of using the generic "everywhere" function with a transform, I use "listify" (which is built on top of "everything")
--to pick out the processes that are failing the check
    
--Returns Nothing if the check is fine, or Just [A.Process] if there is an error (listing all processes that are in error)
parUsageCheck :: A.Process -> Maybe [A.Process]
parUsageCheck proc
  = case listify doUsageCheck proc of
        [] -> Nothing
        x -> Just x
  where
    doUsageCheck :: A.Process -> Bool
    doUsageCheck (A.Par _ _ s) 
      --Looking at the AST Parse for occam, we can either have:
      --A.Par _ _ (A.Several _ [A.OnlyP _ _])
      --A.Par _ _ (A.Rep _ _ (A.OnlyP _ _))
      --Therefore skipSpecs shouldn't be necessary, but I may as well keep it in for now:
      = case skipSpecs s of 
          A.Several _ structList -> 
            --Need to check that for each written item, it is not read/written elsewhere:
            or $ permuteHelper usageCheckList (map getVars structList)
          A.Rep _ rep (A.OnlyP _ proc) ->
            False --TODO!
    doUsageCheck _ = False
    
    --Recursively skips down past the Specs:
    skipSpecs :: A.Structured -> A.Structured
    skipSpecs (A.Spec _ _ s) = skipSpecs s
    skipSpecs other = other
    
    --We need to check: 
    --a) Should be no intersection between our written items, and any written or read items anywhere else
    --b) You may only use a variable subscript if the array is not used anywhere else in the PAR
    --We don't actually need to check for constant subscripts being the same - we assume constant folding has already
    --taken place, which means that a[0] and a[0] will be picked up by the first check (a).  This also assumes
    --that all array index literals will have been converted into INT literals rather than any other type.   
    --The occam 2 manual says the types must be type INT, so this seems like an okay assumption.
    usageCheckList :: WrittenRead -> [WrittenRead] -> Bool
    usageCheckList (written,read) others 
      = ((length (intersect written (allOtherWritten ++ allOtherRead))) /= 0)
        || ((length (intersect (varSubscriptedArrays written) (subscriptedArrays (allOtherWritten ++ allOtherRead)))) /= 0)
        where 
          allOtherWritten = concatMap fst others
          allOtherRead = concatMap snd others
          
          --Takes in the subscripted compound variables, and returns the *array* variables (not the subscripted compounds)
          varSubscriptedArrays :: [A.Variable] -> [A.Variable]
          varSubscriptedArrays = mapMaybe varSubscriptedArrays'
          
          varSubscriptedArrays' :: A.Variable -> Maybe A.Variable 
          varSubscriptedArrays' (A.SubscriptedVariable _ s v) 
            = case ((length . snd . removeDupWR) (everything concatWR (([],[]) `mkQ` getVarExp) s)) of 
                0 -> Nothing
                _ -> Just v
          varSubscriptedArrays' _ = Nothing

          --Takes in the subscripted compound variables, and returns the *array* variables (not the subscripted compounds)
          subscriptedArrays :: [A.Variable] -> [A.Variable]
          subscriptedArrays = mapMaybe subscriptedArrays'
          
          subscriptedArrays' :: A.Variable -> Maybe A.Variable
          subscriptedArrays' (A.SubscriptedVariable _ _ v) = Just v
          subscriptedArrays' _ = Nothing
-}

-- | A custom Set wrapper that allows for easy representation of the "everything" set.
-- In most instances, we could actually build the everything set, but
-- representing it this way is easier, more efficient, and more readable.
-- As you would expect, Everything `intersection` x = x, and Everything `union` x = Everything.
data Ord a => ExSet a = Everything | NormalSet (Set.Set a) deriving (Eq, Show)

intersection :: Ord a => ExSet a -> ExSet a -> ExSet a
intersection Everything x = x
intersection x Everything = x
intersection (NormalSet a) (NormalSet b) = NormalSet (Set.intersection a b)

union :: Ord a => ExSet a -> ExSet a -> ExSet a
union Everything _ = Everything
union _ Everything = Everything
union (NormalSet a) (NormalSet b) = NormalSet (Set.union a b)

unions :: Ord a => [ExSet a] -> ExSet a
unions [] = emptySet
unions ss = foldl1 union ss

emptySet :: Ord a => ExSet a
emptySet = NormalSet (Set.empty)

isSubsetOf :: Ord a => ExSet a -> ExSet a -> Bool
-- Clause order is important here.  Everything is a subset of Everything so this must come first:
isSubsetOf _ Everything = True
isSubsetOf Everything _ = False
isSubsetOf (NormalSet a) (NormalSet b) = Set.isSubsetOf a b



-- TODO have some sort of error-message return if the check fails or if the code fails
checkInitVar :: FlowGraph (Maybe Decl, Vars) -> Node -> Either String ()
checkInitVar graph startNode
  = do vwb <- varWrittenBefore
       mapM_ (checkInitVar' vwb) (map readNode (labNodes graph))
  where
    readNode :: (Node, FNode (Maybe Decl, Vars)) -> (Node, ExSet Var)
    readNode (n, Node (_,(_,Vars read _ _ _))) = (n,NormalSet read)
  
    writeNode :: FNode (Maybe Decl, Vars) -> ExSet Var
    writeNode (Node (_,(_,Vars _ _ written _))) = NormalSet written
    
    -- Nothing is treated as if were the set of all possible variables (easier than building that set):
    nodeFunction :: (Node, EdgeLabel) -> ExSet Var -> Maybe (ExSet Var) -> ExSet Var
    nodeFunction (n,_) inputVal Nothing = union inputVal (maybe emptySet writeNode (lab graph n))    
    nodeFunction (n, EEndPar _) inputVal (Just prevAgg) = unions [inputVal,prevAgg,maybe emptySet writeNode (lab graph n)]
    nodeFunction (n, _) inputVal (Just prevAgg) = intersection prevAgg $ union inputVal (maybe emptySet writeNode (lab graph n))
  
    graphFuncs :: GraphFuncs Node EdgeLabel (ExSet Var)
    graphFuncs = GF
      {
       nodeFunc = nodeFunction
       ,prevNodes = lpre graph
       ,nextNodes = lsuc graph
       ,initVal = emptySet
       ,defVal = Everything
      }
  
    varWrittenBefore :: Either String (Map.Map Node (ExSet Var))
    varWrittenBefore = flowAlgorithm graphFuncs (nodes graph) startNode

    checkInitVar' :: Map.Map Node (ExSet Var) -> (Node, ExSet Var) -> Either String ()
    checkInitVar' writtenMap (n,v)
      = case Map.lookup n writtenMap of
          Nothing -> throwError $ "Variable that is read from: " ++ show (lab graph n) ++ " is never written to"
          -- All read vars should be in the previously-written set
          Just vs -> if v `isSubsetOf` vs then return () else 
            throwError $ "Variable read from: " ++ show (lab graph n) ++ " is not written to before-hand, sets: " ++ show v ++ " and " ++ show vs
              ++ " writtenMap: " ++ show writtenMap

