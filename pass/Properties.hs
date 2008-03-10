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

module Properties
  ( agg_namesDone
  , agg_functionsGone
  , agg_typesDone
  , afterRemoved
  , allChansToAnyOrProtocol
  , arrayLiteralsExpanded
  , arraySizesDeclared
  , assignFlattened
  , assignParRemoved
  , constantsFolded
  , declarationsUnique
  , declarationTypesRecorded
  , declaredNamesResolved
  , eachRangeTransformed
  , eachTransformed
  , expressionTypesChecked
  , freeNamesToArgs
  , functionCallsRemoved
  , functionsRemoved
  , inferredTypesRecorded
  , inputCaseRemoved
  , intLiteralsInBounds
  , mainTagged
  , nestedPulled
  , noInt
  , outExpressionRemoved
  , parsIdentified
  , parsWrapped
  , parUsageChecked
  , processTypesChecked
  , rainParDeclarationsPulledUp
  , rangeTransformed
  , seqInputsFlattened
  , slicesSimplified
  , subscriptsPulledUp
  , typesResolvedInAST
  , typesResolvedInState
  , waitForRemoved
  )
  where

import Control.Monad
import Data.Generics
import Data.Int
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Word
import Text.Regex

import qualified AST as A
import CompState
import Errors
import Metadata
import Pass
import PrettyShow
import Types
import Utils

agg_namesDone :: [Property]
agg_namesDone = [declarationsUnique, declarationTypesRecorded, inferredTypesRecorded, declaredNamesResolved]

agg_typesDone :: [Property]
agg_typesDone = [expressionTypesChecked, inferredTypesRecorded, processTypesChecked, typesResolvedInAST, typesResolvedInState]

agg_functionsGone :: [Property]
agg_functionsGone = [functionCallsRemoved, functionsRemoved]

-- Mark out all the checks I still need to implement:
checkTODO :: Monad m => A.AST -> m ()
checkTODO _ = return ()

-- For properties that can't easily be tested (such as properties that are themselves tests anyway!)
nocheck :: Monad m => A.AST -> m ()
nocheck _ = return ()

getDeclaredNames :: A.AST -> [A.Name]
getDeclaredNames = everything (++) ([] `mkQ` find)
  where
    find :: A.Specification -> [A.Name]
    find (A.Specification _ n (A.Declaration {})) = [n]
    find _ = []

checkNull :: (Data a, Die m) => String -> [a] -> m ()
checkNull _ [] = return ()
checkNull s xs = dieP (findMeta xs) $ "Property check " ++ show s ++ " failed: " ++ pshow xs

isNonceOrUnique :: String -> Bool
isNonceOrUnique nm = isJust $ matchRegex (mkRegex ".*_[a-z][0-9]+$") nm

declaredNamesResolved :: Property
declaredNamesResolved = Property "declaredNamesResolved" $
  checkNull "namesResolved" . filter (not . isNonceOrUnique . A.nameName) . getDeclaredNames

noInt :: Property
noInt = Property "noInt" $
  checkNull "noInt" . listify (== A.Int)

declarationTypesRecorded :: Property
declarationTypesRecorded = Property "declarationTypesRecorded" $ \t ->
  do let decls = getDeclaredNames t
     st <- getCompState
     mapM_ (checkName (csNames st)) decls
  where
    checkName :: Die m => Map.Map String A.NameDef -> A.Name -> m ()
    checkName nms n = case Map.lookup (A.nameName n) nms of
      Nothing -> dieP m $ "Type of name " ++ show (A.nameName n) ++ " was not recorded"
      Just nd -> when (A.ndName nd /= A.nameName n) $
                   dieP m $ "Name not recorded correctly: " ++ show (A.nameName n)
     where m = A.nameMeta n

declarationsUnique :: Property
declarationsUnique = Property "declarationsUnique" $
     checkDupes . sort . getDeclaredNames
  where
    checkDupes :: Die m => [A.Name] -> m ()
    checkDupes [] = return ()
    checkDupes (n:[]) = return ()
    checkDupes (n:n':ns)
      = do when (A.nameName n == A.nameName n') $
             dieP (A.nameMeta n) $ "Duplicate definition of name (names not uniquified successfully?) " ++ show (A.nameName n) ++ " with: " ++ show (A.nameMeta n')
           checkDupes (n':ns)

constantsFolded :: Property
constantsFolded = Property "constantsFolded" checkTODO

intLiteralsInBounds :: Property
intLiteralsInBounds = Property "intLiteralsInBounds" $
  mapM_ check . everything (++) ([] `mkQ` find)
  where
    find :: A.Expression -> [(Meta, A.Type, String)]
    find (A.Literal m t (A.IntLiteral _ s)) = [(m,t,s)]
    find _ = []
    
    toPair :: (Monad m, Integral a) => [a] -> m (Integer, Integer)
    toPair [x,y] = return (toInteger x, toInteger y)
    
    occToBounds :: Die m => Meta -> A.Type -> m (Integer, Integer)
    occToBounds _ A.Byte = toPair ([minBound, maxBound] :: [Word8])
    occToBounds _ A.UInt16 = toPair ([minBound, maxBound] :: [Word16])
    occToBounds _ A.UInt32 = toPair ([minBound, maxBound] :: [Word32])
    occToBounds _ A.UInt64 = toPair ([minBound, maxBound] :: [Word64])
    occToBounds _ A.Int8 = toPair ([minBound, maxBound] :: [Int8])
    occToBounds _ A.Int16 = toPair ([minBound, maxBound] :: [Int16])
    occToBounds _ A.Int32 = toPair ([minBound, maxBound] :: [Int32])
    occToBounds _ A.Int = toPair ([minBound, maxBound] :: [Int32])
    occToBounds _ A.Int64 = toPair ([minBound, maxBound] :: [Int64])
    occToBounds m t = dieP m $ "Type " ++ show t ++ " is not an integer type"

    check :: Die m => (Meta, A.Type, String) -> m ()
    check (m, t, s)
      = do (low, high) <- occToBounds m t
           when (n < low) $ dieP m $ "Integer not within lower bound: " ++ s
           when (n > high) $ dieP m $ "Integer not within upper bound: " ++ s
      where
        n :: Integer
        n = read s

expressionTypesChecked :: Property
expressionTypesChecked = Property "expressionTypesChecked" nocheck

processTypesChecked :: Property
processTypesChecked = Property "processTypesChecked" nocheck

eachRangeTransformed :: Property
eachRangeTransformed = Property "eachRangeTransformed" checkTODO

eachTransformed :: Property
eachTransformed = Property "eachTransformed" checkTODO

rangeTransformed :: Property
rangeTransformed = Property "rangeTransformed" checkTODO

rainParDeclarationsPulledUp :: Property
rainParDeclarationsPulledUp = Property "rainParDeclarationsPulledUp" checkTODO

inferredTypesRecorded :: Property
inferredTypesRecorded = Property "inferredTypesRecorded" checkTODO

findUDT :: A.Type -> Bool
findUDT (A.UserDataType {}) = True
findUDT _ = False

typesResolvedInAST :: Property
typesResolvedInAST = Property "typesResolvedInAST" $
  checkNull "typesResolvedInAST" . listify findUDT

typesResolvedInState :: Property
typesResolvedInState = Property "typesResolvedInState" $
  \t -> checkNull "typesResolvedInState" . listify findUDT =<< getCompState

checkAllExprVariable :: Die m => [A.Expression] -> m ()
checkAllExprVariable = mapM_ check
  where
    check :: Die m => A.Expression -> m ()
    check (A.ExprVariable {}) = return ()
    check e = dieP (findMeta e) $ "Found something that was not an expression variable: " ++ pshow e

findOutputExprs :: A.OutputItem -> [A.Expression]
findOutputExprs (A.OutExpression _ e) = [e]
findOutputExprs (A.OutCounted _ ce ae) = [ce, ae]

outExpressionRemoved :: Property
outExpressionRemoved = Property "outExpressionRemoved" $
  checkAllExprVariable . everything (++) ([] `mkQ` findOutputExprs)

findInputCase :: A.InputMode -> Bool
findInputCase (A.InputCase {}) = True
findInputCase _ = False

inputCaseRemoved :: Property
inputCaseRemoved = Property "inputCaseRemoved" $
  checkNull "inputCaseRemoved" . listify findInputCase

findParAssign :: A.Process -> Bool
findParAssign (A.Assign _ (_:_:_) _) = True
findParAssign _ = False

assignParRemoved :: Property
assignParRemoved = Property "assignParRemoved" $
  checkNull "assignParRemoved" . listify findParAssign

findParWithProcess :: A.Process -> Bool
findParWithProcess (A.Par _ _ s) = findParProcess s
  where
    -- We don't use listify here because it would descend into the declarations
    -- of the processes (for the wrapped PARs) and find A.Structured A.Process items
    -- in SEQs in there
    findParProcess :: A.Structured A.Process -> Bool
    findParProcess (A.Only _ (A.ProcCall {})) = False
    findParProcess (A.Only {}) = True
    findParProcess (A.Rep _ _ s) = findParProcess s
    findParProcess (A.ProcThen _ _ s) = findParProcess s
    findParProcess (A.Spec _ _ s) = findParProcess s
    findParProcess (A.Several _ ss) = or $ map findParProcess ss
findParWithProcess _ = False
    
parsWrapped :: Property
parsWrapped = Property "parsWrapped" $
  checkNull "parsWrapped" . listify findParWithProcess

findAssignVars :: A.Process -> [A.Variable]
findAssignVars (A.Assign _ vs _) = vs
findAssignVars _ = []

filterArrayAndRecord :: (CSMR m, Die m) => A.Variable -> m Bool
filterArrayAndRecord v
  = do t <- typeOfVariable v
       return $ case t of
         A.Array {} -> True
         A.Record {} -> True
         _ -> False

assignFlattened :: Property
assignFlattened = Property "assignFlattened" $
  checkNull "assignFlattened" <.< (filterM filterArrayAndRecord . everything (++) ([] `mkQ` findAssignVars))

parUsageChecked :: Property
parUsageChecked = Property "parUsageChecked" nocheck

freeNamesToArgs :: Property
freeNamesToArgs = Property "freeNamesToArgs" checkTODO

nestedPulled :: Property
nestedPulled = Property "nestedPulled" checkTODO

findFunctions :: A.SpecType -> Bool
findFunctions (A.Function {}) = True
findFunctions _ = False

functionsRemoved :: Property
functionsRemoved = Property "functionsRemoved" $
  checkNull "functionsRemoved" . listify findFunctions

afterRemoved :: Property
afterRemoved = Property "afterRemoved" $
  checkNull "afterRemoved" . listify (== A.After)

arrayLiteralsExpanded :: Property
arrayLiteralsExpanded = Property "arrayLiteralsExpanded" checkTODO

findFunctionCalls :: A.Expression -> Bool
findFunctionCalls (A.FunctionCall {}) = True
findFunctionCalls _ = False

findFunctionCallLists :: A.ExpressionList -> Bool
findFunctionCallLists (A.FunctionCallList {}) = True
findFunctionCallLists _ = False

functionCallsRemoved :: Property
functionCallsRemoved = Property "functionCallsRemoved" $
  \t -> checkNull "functionCallsRemoved/1" (listify findFunctionCalls t) >> checkNull "functionCallsRemoved/2" (listify findFunctionCallLists t)

subscriptsPulledUp :: Property
subscriptsPulledUp = Property "subscriptsPulledUp" checkTODO

parsIdentified :: Property
parsIdentified = Property "parsIdentified" nocheck

findWaitFor :: A.Alternative -> Bool
findWaitFor (A.AlternativeWait _ A.WaitFor _ _) = True
findWaitFor _ = False

waitForRemoved :: Property
waitForRemoved = Property "waitForRemoved" $
  checkNull "waitForRemoved" . listify findWaitFor


allChansToAnyOrProtocol :: Property
allChansToAnyOrProtocol = Property "allChansToAnyOrProtocol" checkTODO

mainTagged :: Property
mainTagged = Property "mainTagged" nocheck
-- We don't check this because not having a main process may be valid in the future
-- so there's no easy way to check if the main process has been looked for or not

seqInputsFlattened :: Property
seqInputsFlattened = Property "seqInputsFlattened" $ checkNull "seqInputsFlattened" . listify findMultipleInputs
  where
    findMultipleInputs :: A.InputMode -> Bool
    findMultipleInputs (A.InputSimple _ (_:_:_)) = True
    findMultipleInputs _ = False

arraySizesDeclared :: Property
arraySizesDeclared = Property "arraySizesDeclared" nocheck

slicesSimplified :: Property
slicesSimplified = Property "slicesSimplified" $
  checkNull "slicesSimplified" . listify findJustFromOrFor
  where
    findJustFromOrFor :: A.Subscript -> Bool
    findJustFromOrFor (A.SubscriptFrom {}) = True
    findJustFromOrFor (A.SubscriptFor {}) = True
    findJustFromOrFor _ = False
