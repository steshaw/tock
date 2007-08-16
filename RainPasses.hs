module RainPasses where

import TestUtil

--TODO add passes for:
--  Typing the variables
--  Resolving (and uniquifying) names


rainPasses :: A.Process -> PassM A.Process
rainPasses = runPasses passes
  where
    passes = 
    [ ("Convert seqeach/pareach loops into classic replicated SEQ/PAR",transformEach)
    ]

--TODO test this pass and then tidy it up
transformEach :: Data t => t -> PassM t
transformEach = everywhere (mkM transformEach')
  where
    transformEach' :: A.Structured -> A.Structured
    transformEach' (A.Rep m (A.ForEach m' loopVar loopExp) s)
      = do (spec,var) <- case loopExp of
             (A.ExprVariable _ v) -> return (\x -> x,v)
             _ -> do t <- typeOfExpression loopExp
                     spec@(A.Specification _ n' _) <- makeNonceIsExpr "loopVar" m t loopExp 
                     return (\x -> A.Specification m spec x,A.Variable m n')
           --spec is a function A.Structured -> A.Structured, var is an A.Variable
           
           loopVarType <- typeOfVariable loopVar
           loopIndex <- makeNonce "loopIndex"
           let newRep = A.For m' (simpleName loopIndex) (intLiteral 0) (A.SizeVariable m' var)
           let s' = A.Spec m' (A.Specification m' loopVar (A.Is m' A.Abbrev loopVarType (A.SubscriptedVariable m' (A.Subscript m' (A.ExprVariable m' (variable loopIndex)))  var) )) s           
           return (spec (A.Rep m newRep s'))             
    transformEach' s = s
