module RainPasses where

import TestUtil
import qualified AST as A
import Pass
import Data.Generics
import Types
import CompState

--TODO add passes for:
--  Typing the variables


rainPasses :: A.Process -> PassM A.Process
rainPasses = runPasses passes
  where
    passes = 
     [ ("Uniquify variable declarations and resolve variable names",uniquifyAndResolveVars)
       ,("Record name types in dictionary",recordNameTypes)
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

recordNameTypes :: Data t => t -> PassM t
recordNameTypes = return


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
