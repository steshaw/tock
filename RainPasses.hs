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

module RainPasses where

import TestUtil
import qualified AST as A
import Pass
import Data.Generics
import Types
import CompState
import Errors

rainPasses :: A.Process -> PassM A.Process
rainPasses = runPasses passes
  where
    passes = 
     [ ("Uniquify variable declarations and resolve variable names",uniquifyAndResolveVars)
       ,("Record declared name types in dictionary",recordDeclNameTypes)
       ,("Record inferred name types in dictionary",recordInfNameTypes)
       ,("Convert seqeach/pareach loops into classic replicated SEQ/PAR",transformEach)
     ]

uniquifyAndResolveVars :: Data t => t -> PassM t
uniquifyAndResolveVars = everywhereM (mkM uniquifyAndResolveVars')
  where
    uniquifyAndResolveVars' :: A.Structured -> PassM A.Structured
    uniquifyAndResolveVars' (A.Spec m (A.Specification m' n decl@(A.Declaration _ _)) scope) 
      = do n' <- makeNonce $ A.nameName n
           let scope' = everywhere (mkT $ replaceNameName (A.nameName n) n') scope
           return $ A.Spec m (A.Specification m' n {A.nameName = n'} decl) scope'
    uniquifyAndResolveVars' s = return s

    replaceNameName :: String -> String -> A.Name -> A.Name
    replaceNameName find replace n = if (A.nameName n) == find then n {A.nameName = replace} else n

recordDeclNameTypes :: Data t => t -> PassM t
recordDeclNameTypes = everywhereM (mkM recordDeclNameTypes')
  where
    recordDeclNameTypes' :: A.Specification -> PassM A.Specification
    recordDeclNameTypes' input@(A.Specification m n decl@(A.Declaration _ declType)) 
      = defineName n A.NameDef {A.ndMeta = m, A.ndName = A.nameName n, A.ndOrigName = A.nameName n, 
                                A.ndNameType = A.VariableName, A.ndType = decl, 
                                A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}
        >> return input	
    recordDeclNameTypes' s = return s

recordInfNameTypes :: Data t => t -> PassM t
recordInfNameTypes = everywhereM (mkM recordInfNameTypes')
  where
    recordInfNameTypes' :: A.Replicator -> PassM A.Replicator
    recordInfNameTypes' input@(A.ForEach m n e)
      = do arrType <- typeOfExpression e
           innerT <- case arrType of 
             A.Array (_:innerDims) t ->
               return $ case innerDims of 
                 [] -> t
                 _ -> A.Array innerDims t               
             _ -> dieP m "Cannot do a foreach loop over a non-array type (or array with zero dimensions)"
           defineName n A.NameDef {A.ndMeta = m, A.ndName = A.nameName n, A.ndOrigName = A.nameName n, 
                                   A.ndNameType = A.VariableName, A.ndType = (A.Declaration m innerT), 
                                   A.ndAbbrevMode = A.Original, A.ndPlacement = A.Unplaced}
           return input
    recordInfNameTypes' r = return r


transformEach :: Data t => t -> PassM t
transformEach = everywhereM (mkM transformEach')
  where
    transformEach' :: A.Structured -> PassM A.Structured
    transformEach' (A.Rep m (A.ForEach m' loopVar loopExp) s)
      = do (spec,var) <- case loopExp of
             (A.ExprVariable _ v) -> return (id,v)
             _ -> do t <- typeOfExpression loopExp
                     spec@(A.Specification _ n' _) <- makeNonceIsExpr "loopVar" m t loopExp 
                     return (A.Spec m spec,A.Variable m n')
           --spec is a function A.Structured -> A.Structured, var is an A.Variable
           
           loopVarType <- typeOfName loopVar
           loopIndex <- makeNonce "loopIndex"
           let newRep = A.For m' (simpleName loopIndex) (intLiteral 0) (A.SizeVariable m' var)
           let s' = A.Spec m'
                 (A.Specification m' loopVar
                   (A.Is m' A.Abbrev loopVarType
                     (A.SubscriptedVariable m' (A.Subscript m' (A.ExprVariable m' (variable loopIndex)))  var)
                   )
                 )
                 s
           return (spec (A.Rep m newRep s'))
    transformEach' s = return s
