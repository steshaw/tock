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

-- | This code implements various usage checking.  It is designed to work with
-- the control-flow graph stuff, hence the use of functions that match the dictionary
-- of functions in FlowGraph.  This is also why we don't drill down into processes;
-- the control-flow graph means that we only need to concentrate on each node that isn't nested.
module Check (checkInitVar, usageCheckPass) where

import Control.Monad.Identity
import Data.Graph.Inductive
import Data.List hiding (union)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import ArrayUsageCheck
import CompState
import Errors
import FlowAlgorithms
import FlowGraph
import Metadata
import Pass
import ShowCode
import UsageCheckAlgorithms
import UsageCheckUtils

usageCheckPass :: Pass
usageCheckPass t = do g' <- buildFlowGraph labelFunctions t
                      g <- case g' of
                        Left err -> dieP (findMeta t) err
                        Right g -> return g
                      sequence_ $ checkPar checkArrayUsage g
                      return t

   
    {-
      Near the beginning, this piece of code was too clever for itself and applied processVarW using "everything".
      The problem with this is that given var@(A.SubscriptedVariable _ sub arrVar), the functions would be recursively
      applied to sub and arrVar.  processVarW should return var as written to, but never the subscripts in sub; those subscripts are not written to!
      
      Therefore processVarW must *not* be applied using the generics library, and instead should always be applied
      directly to an A.Variable.  Internally it uses the generics library to process the subscripts (using getVarExp)
    -}    
    
    --Pull out all the subscripts into the read category, but leave the given var in the written category:
{-
processVarW :: A.Variable -> Vars
processVarW v = writtenVars [variableToVar v]
    
processVarR :: A.Variable -> Vars
processVarR v = readVars [variableToVar v]

processVarUsed :: A.Variable -> Vars
processVarUsed v = usedVars [variableToVar v]
-}
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

showCodeExSet :: (CSM m, Ord a, ShowOccam a, ShowRain a) => ExSet a -> m String
showCodeExSet Everything = return "<all-vars>"
showCodeExSet (NormalSet s)
    = do ss <- mapM showCode (Set.toList s)
         return $ "{" ++ concat (intersperse ", " ss) ++ "}"

-- | Checks that no variable is used uninitialised.  That is, it checks that every variable is written to before it is read.
checkInitVar :: forall m. (Monad m, Die m, CSM m) => Meta -> FlowGraph m (Maybe Decl, Vars) -> Node -> m ()
checkInitVar m graph startNode
  = do vwb <- case flowAlgorithm graphFuncs (nodes graph) startNode of
         Left err -> dieP m $ "Error building control-flow graph: " ++ err
         Right x -> return x
       -- vwb is a map from Node to a set of Vars that have been written by that point
       -- Now we check that for every variable read in each node, it has already been written to by then
       mapM_ (checkInitVar' vwb) (map readNode (labNodes graph))
  where
    -- Gets all variables read-from in a particular node, and the node identifier
    readNode :: (Node, FNode m (Maybe Decl, Vars)) -> (Node, ExSet Var)
    readNode (n, Node (_,(_,Vars read _ _),_)) = (n,NormalSet read)
  
    -- Gets all variables written-to in a particular node
    writeNode :: FNode m (Maybe Decl, Vars) -> ExSet Var
    writeNode (Node (_,(_,Vars _ written _),_)) = NormalSet written
    
    -- Nothing is treated as if were the set of all possible variables:
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
      
    getMeta :: Node -> Meta
    getMeta n = case lab graph n of
      Just (Node (m,_,_)) -> m
      _ -> emptyMeta
        
    checkInitVar' :: Map.Map Node (ExSet Var) -> (Node, ExSet Var) -> m ()
    checkInitVar' writtenMap (n,v)
      = let vs = fromMaybe emptySet (Map.lookup n writtenMap) in
        -- The read-from set should be a subset of the written-to set:
        if v `isSubsetOf` vs then return () else 
          do readVars <- showCodeExSet v
             writtenVars <- showCodeExSet vs
             dieP (getMeta n) $ "Variable read from is not written to before-hand, sets are read: " ++ show readVars ++ " and written: " ++ show writtenVars
