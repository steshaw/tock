module UsageCheck where

import qualified AST as A
import Data.Generics
import Metadata
import Data.List

--An obvious thing to do would be to hold these lists (of written/read variables respectively) instead as sets
--However, this would involve defining an ordering over A.Variable.  This would be do-able for plain A.Variables,
--but in order to define a proper ordering for subscripted variables, we would end up needing to provide an
--ordering for A.Expression (and all its subtypes)!  Therefore, they are kept simply as lists:

type WrittenRead = ([A.Variable],[A.Variable])

concatWR :: WrittenRead -> WrittenRead -> WrittenRead
concatWR (w0,r0) (w1,r1) = (w0 ++ w1,r0 ++ r1)

foldWR :: [WrittenRead] -> WrittenRead
foldWR = foldl1 concatWR

removeDupWR :: WrittenRead -> WrittenRead
removeDupWR (w,r) = (nub w,nub r)


--Gets the (written,read) variables of a piece of an occam program:

--For subscripted variables used as Lvalues , e.g. a[b] it should return a[b] as written-to and b as read
--For subscripted variables used as expressions, e.g. a[b] it should return a[b],b as read (with no written-to)

getVars :: Data t => t -> WrittenRead
getVars 
  = removeDupWR . (everything concatWR (([],[]) 
    `mkQ` getVarProc
    ))
  where
    getVarProc :: A.Process -> WrittenRead   
    getVarProc (A.Assign _ vars expList) 
        --Join together:
      = concatWR 
          --The written-to variables on the LHS:
          (foldWR (map processVarW vars)) 
          --All variables read on the RHS:
          (everything concatWR (([],[]) `mkQ` getVarExp) expList)
    --TODO output input etc (all other processes that directly write to/read from variables)
    getVarProc _ = ([],[])
    
    {-
      Near the beginning, this piece of code was too clever for itself and applied processVarW using "everything".
      The problem with this is that given var@(A.SubscriptedVariable _ sub arrVar), the functions would be recursively
      applied to sub and arrVar.  processVarW should return var, but never the subscripts in sub; those subscripts are not written to!
      
      Therefore processVarW must *not* be applied using the generics library, and instead should always be applied
      directly to an A.Variable.  Internally it uses the generics library to process the subscripts (using getVarExp)
    -}    
    
    --Pull out all the subscripts into the read category, but leave the given var in the written category:
    processVarW :: A.Variable -> WrittenRead
    processVarW v@(A.Variable _ _) = ([v],[])
    processVarW v@(A.SubscriptedVariable _ s _) = concatWR ([v],[]) (everything concatWR (([],[]) `mkQ` getVarExp) s) 

    --Only need to deal with the two cases where we can see an A.Variable directly;
    --the generic recursion will take care of nested expressions, and even the expressions used as subscripts
    getVarExp :: A.Expression -> WrittenRead
    getVarExp (A.SizeVariable _ v) = ([],[v])
    getVarExp (A.ExprVariable _ v) = ([],[v])
    getVarExp _ = ([],[])


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
      --TODO deal with Rep and Spec inside Par
      = case s of 
          A.Several _ structList -> 
            --Need to check that for each written item, it is not read/written elsewhere:
            or $ permuteHelper usageCheckList (map getVars structList)
    doUsageCheck _ = False
    
    --Should be no intersection between our written items, and any written or read items anywhere else:
    usageCheckList :: WrittenRead -> [WrittenRead] -> Bool
    usageCheckList (written,read) others 
      = (length (intersect written (allOtherWritten ++ allOtherRead))) /= 0
        where 
          allOtherWritten = concatMap fst others
          allOtherRead = concatMap snd others
