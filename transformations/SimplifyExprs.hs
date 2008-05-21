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

-- | Simplify expressions in the AST.
module SimplifyExprs where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map

import qualified AST as A
import CompState
import Errors
import EvalConstants
import Metadata
import Pass
import qualified Properties as Prop
import ShowCode
import Types
import Utils

simplifyExprs :: [Pass]
simplifyExprs = makePassesDep
      [ ("Convert FUNCTIONs to PROCs", functionsToProcs, Prop.agg_namesDone ++ [Prop.expressionTypesChecked, Prop.parUsageChecked,
        Prop.functionTypesChecked], [Prop.functionsRemoved])
      , ("Convert AFTER to MINUS", removeAfter, [Prop.expressionTypesChecked], [Prop.afterRemoved])
      , ("Expand array literals", expandArrayLiterals, [Prop.expressionTypesChecked, Prop.processTypesChecked], [Prop.arrayLiteralsExpanded])
      , ("Pull up replicator counts for SEQs", pullRepCounts, Prop.agg_namesDone ++ Prop.agg_typesDone,  [])
      , ("Pull up definitions", pullUp False, Prop.agg_namesDone ++ Prop.agg_typesDone ++ [Prop.functionsRemoved, Prop.seqInputsFlattened], [Prop.functionCallsRemoved, Prop.subscriptsPulledUp])
      , ("Transform array constructors into initialisation code", transformConstr, Prop.agg_namesDone ++ Prop.agg_typesDone
        ++ [Prop.subscriptsPulledUp], [Prop.arrayConstructorsRemoved])
      ]
--      ++ makePassesDep' ((== BackendCPPCSP) . csBackend) [("Pull up definitions (C++)", pullUp True, Prop.agg_namesDone ++ [Prop.expressionTypesChecked, Prop.functionsRemoved, Prop.processTypesChecked,Prop.seqInputsFlattened], [Prop.functionCallsRemoved, Prop.subscriptsPulledUp])]

-- | Convert FUNCTION declarations to PROCs.
functionsToProcs :: Data t => t -> PassM t
functionsToProcs = doGeneric `extM` doSpecification
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric functionsToProcs

    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification (A.Specification m n (A.Function mf sm rts fs evp))
        = do -- Create new names for the return values.
             specs <- sequence [makeNonceVariable "return_formal" mf t A.VariableName A.Abbrev | t <- rts]
             let names = [n | A.Specification mf n _ <- specs]
             -- Note the return types so we can fix calls later.
             modify $ (\ps -> ps { csFunctionReturns = Map.insert (A.nameName n) rts (csFunctionReturns ps) })
             -- Turn the value process into an assignment process.
             let p = vpToSeq m n evp [A.Variable mf n | n <- names]
             let st = A.Proc mf sm (fs ++ [A.Formal A.Abbrev t n | (t, n) <- zip rts names]) p
             -- Build a new specification and redefine the function.
             let spec = A.Specification m n st
             let nd = A.NameDef {
                        A.ndMeta = mf,
                        A.ndName = A.nameName n,
                        A.ndOrigName = A.nameName n,
                        A.ndNameType = A.ProcName,
                        A.ndSpecType = st,
                        A.ndAbbrevMode = A.Original,
                        A.ndPlacement = A.Unplaced
                      }
             defineName n nd
             doGeneric spec
    doSpecification s = doGeneric s

    vpToSeq :: Meta -> A.Name -> Either (A.Structured A.ExpressionList) A.Process -> [A.Variable] -> A.Process
    vpToSeq m n (Left el) vs = A.Seq m $ vpToSeq' el vs
    vpToSeq _ n (Right p) vs = subst p
      where
        subst :: Data t => t -> t
        subst = doGenericSubst `extT` doAssignSubst
        
        doGenericSubst :: Data t => t -> t
        doGenericSubst = gmapT subst `extT` (id :: String -> String) `extT` (id :: Meta -> Meta)
        
        doAssignSubst :: A.Process -> A.Process
        doAssignSubst ass@(A.Assign m [A.Variable _ dest] el) = if (A.nameName dest == A.nameName n) then (A.Assign m vs el) else ass
        doAssignSubst p = doGenericSubst p
        

    vpToSeq' :: A.Structured A.ExpressionList -> [A.Variable] -> A.Structured A.Process
    vpToSeq' (A.Spec m spec s) vs = A.Spec m spec (vpToSeq' s vs)
    vpToSeq' (A.ProcThen m p s) vs = A.ProcThen m p (vpToSeq' s vs)
    vpToSeq' (A.Only m el) vs = A.Only m $ A.Assign m vs el

-- | Convert AFTER expressions to the equivalent using MINUS (which is how the
-- occam 3 manual defines AFTER).
removeAfter :: Data t => t -> PassM t
removeAfter = doGeneric `extM` doExpression
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric removeAfter

    doExpression :: A.Expression -> PassM A.Expression
    doExpression (A.Dyadic m A.After a b)
        =  do a' <- removeAfter a
              b' <- removeAfter b
              t <- astTypeOf a'
              case t of
                A.Byte -> do let one = A.Literal m t $ A.IntLiteral m "1"
                                 oneTwoSeven = A.Literal m t $ A.IntLiteral m "127"
                             return $ A.Dyadic m A.Less (A.Dyadic m A.Minus (A.Dyadic m A.Minus a' b') one) oneTwoSeven
                _ -> do let zero = A.Literal m t $ A.IntLiteral m "0"
                        return $ A.Dyadic m A.More (A.Dyadic m A.Minus a' b') zero
    doExpression e = doGeneric e

-- | For array literals that include other arrays, burst them into their elements.
expandArrayLiterals :: Data t => t -> PassM t
expandArrayLiterals = doGeneric `extM` doArrayElem
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric expandArrayLiterals

    doArrayElem :: A.ArrayElem -> PassM A.ArrayElem
    doArrayElem ae@(A.ArrayElemExpr e)
        =  do e' <- expandArrayLiterals e
              t <- astTypeOf e'
              case t of
                A.Array ds _ -> expand ds e
                _ -> doGeneric ae
    doArrayElem ae = doGeneric ae

    expand :: [A.Dimension] -> A.Expression -> PassM A.ArrayElem
    expand [] e = return $ A.ArrayElemExpr e
    expand (A.UnknownDimension:_) e
        = dieP (findMeta e) "array literal containing non-literal array of unknown size"
    expand (A.Dimension n:ds) e
        =  do -- Because it's an array literal, we must know the size.
              size <- evalIntExpression n
              elems <- sequence [expand ds (A.SubscriptedExpr m
                                             (A.Subscript m A.NoCheck $
                                               makeConstant m i) e)
                                 | i <- [0 .. size - 1]]
              return $ A.ArrayElemArray elems
      where m = findMeta e

-- | We pull up the loop (Rep) counts into a temporary expression, whenever the loop
-- count could be modified within the loop.  Here are all things that can be replicated:
-- SEQ -- can be altered during the loop, must pull up
-- PAR -- count cannot be modified by code inside the loop (it is used before any PAR branches are run)
-- IF  -- cannot be altered during loop; once body executes, loop is effectively broken
-- ALT -- same as IF
-- Therefore, we only need to pull up the counts for sequential replicators
--
-- TODO for simplification, we could avoid pulling up replication counts that are known to be constants
pullRepCounts :: Data t => t -> PassM t
pullRepCounts = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric pullRepCounts
    
    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Seq m s) = pullRepCountSeq s >>* A.Seq m
    doProcess p = doGeneric p
    
    pullRepCountSeq :: A.Structured A.Process -> PassM (A.Structured A.Process)
    pullRepCountSeq (A.Only m p) = doProcess p >>* A.Only m
    pullRepCountSeq (A.Spec m sp str)
      = do sp' <- pullRepCounts sp
           str' <- pullRepCountSeq str
           return $ A.Spec m sp' str'
    pullRepCountSeq (A.ProcThen m p s)
      = do p' <- doProcess p
           s' <- pullRepCountSeq s
           return $ A.ProcThen m p' s'
    pullRepCountSeq (A.Several m ss) = mapM pullRepCountSeq ss >>* A.Several m
    pullRepCountSeq (A.Rep m (A.For m' n from for) s)
      = do t <- astTypeOf for
           spec@(A.Specification _ nonceName _) <- makeNonceIsExpr "rep_for" m' t for
           s' <- pullRepCountSeq s
           return $ A.Spec m spec $ A.Rep m (A.For m' n from (A.ExprVariable m' $ A.Variable m' nonceName)) s'
    -- Other replicators (such as ForEach)
    pullRepCountSeq (A.Rep m rep s)
      = do s' <- pullRepCountSeq s
           return $ A.Rep m rep s'

transformConstr :: Data t => t -> PassM t
transformConstr = doGeneric `ext1M` doStructured
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric transformConstr

    -- For arrays, this takes a constructor expression:
    --   VAL type name IS [i = rep | expr]:
    --   ...
    -- and produces this:
    --   type name:
    --   PROCTHEN
    --     INT indexvar:
    --     SEQ
    --       indexvar := 0
    --       SEQ i = rep
    --         SEQ
    --           name[indexvar] := expr
    --           indexvar := indexvar + 1
    --     ...
    --
    -- For lists, it takes the similar expression and produces:
    -- type name:
    -- PROCTHEN
    --   SEQ i = rep
    --     name += [expr]
    doStructured :: Data a => A.Structured a -> PassM (A.Structured a)
    doStructured (A.Spec m (A.Specification m' n (A.IsExpr _ _ _ expr@(A.ExprConstr m'' (A.RepConstr _ t rep exp)))) scope)
      = do scope' <- transformConstr scope
           case t of
             A.Array {} ->
               do indexVarSpec@(A.Specification _ indexName _) <- makeNonceVariable "array_constr_index" m'' A.Int A.VariableName A.Original
                  let indexVar = A.Variable m'' indexName
                  
                  return $ declDest $ A.ProcThen m''
                    (A.Seq m'' $ A.Spec m'' indexVarSpec $
                      A.Several m'' [assignIndex0 indexVar,
                        A.Rep m'' rep $ A.Only m'' $ A.Seq m'' $
                          A.Several m''
                            [ assignItem indexVar
                            , incrementIndex indexVar ]
                    ])
                    scope'
             A.List {} ->
               return $ declDest $ A.ProcThen m''
                 (A.Seq m'' $ A.Rep m'' rep $ appendItem)
                 scope'
             _ -> diePC m $ formatCode "Unsupported type for array constructor: %" t
      where
        declDest :: Data a => A.Structured a -> A.Structured a
        declDest = A.Spec m (A.Specification m' n (A.Declaration m' t))

        assignIndex0 :: A.Variable -> A.Structured A.Process
        assignIndex0 indexVar = A.Only m'' $ A.Assign m'' [indexVar] $
          A.ExpressionList m'' [A.Literal m'' A.Int $ A.IntLiteral m'' "0"]

        incrementIndex :: A.Variable -> A.Structured A.Process
        incrementIndex indexVar = A.Only m'' $ A.Assign m'' [indexVar] $
          A.ExpressionList m'' [addOne $ A.ExprVariable m'' indexVar]

        assignItem :: A.Variable -> A.Structured A.Process
        assignItem indexVar = A.Only m'' $ A.Assign m'' [A.SubscriptedVariable m''
          (A.Subscript m'' A.NoCheck $ A.ExprVariable m'' indexVar) $
            A.Variable m'' n] $ A.ExpressionList m'' [exp]

        appendItem :: A.Structured A.Process
        appendItem = A.Only m'' $ A.Assign m'' [A.Variable m'' n] $
          A.ExpressionList m'' [A.Dyadic m'' A.Concat
            (A.ExprVariable m'' $ A.Variable m'' n)
            (A.Literal m'' t $ A.ListLiteral m'' [exp])]

    doStructured s = doGeneric s

-- | Find things that need to be moved up to their enclosing Structured, and do
-- so.
pullUp :: Data t => Bool -> t -> PassM t
pullUp pullUpArraysInsideRecords
       = doGeneric
          `ext1M` doStructured
          `extM` doProcess
          `extM` doSpecification
          `extM` doLiteralRepr
          `extM` doExpression
          `extM` doVariable
          `extM` doExpressionList
  where
    pullUpRecur :: Data t => t -> PassM t
    pullUpRecur = pullUp pullUpArraysInsideRecords
  
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric pullUpRecur

    -- | When we encounter a Structured, create a new pulled items state,
    -- recurse over it, then apply whatever pulled items we found to it.
    doStructured :: Data a => A.Structured a -> PassM (A.Structured a)
    doStructured s
        =  do pushPullContext
              -- Recurse over the body, then apply the pulled items to it
              s' <- doGeneric s >>= applyPulled
              -- ... and restore the original pulled items
              popPullContext
              return s'

    -- | As with doStructured: when we find a process, create a new pulled items
    -- context, and if we find any items apply them to it.
    doProcess :: A.Process -> PassM A.Process
    doProcess p
        =  do pushPullContext
              p' <- doGeneric p
              pulled <- havePulled
              p'' <- if pulled
                       then liftM (A.Seq emptyMeta) $ applyPulled (A.Only emptyMeta p')
                       else return p'
              popPullContext
              return p''

    -- | Filter what can be pulled in Specifications.
    doSpecification :: A.Specification -> PassM A.Specification
    -- Iss might be SubscriptedVars -- which is fine; the backend can deal with that.
    doSpecification (A.Specification m n (A.Is m' am t v))
        =  do v' <- doGeneric v    -- note doGeneric rather than pullUp
              return $ A.Specification m n (A.Is m' am t v')
    -- IsExprs might be SubscriptedExprs, and if so we have to convert them.
    doSpecification (A.Specification m n (A.IsExpr m' am t e))
        =  do e' <- doExpression' e  -- note doExpression' rather than pullUp
              return $ A.Specification m n (A.IsExpr m' am t e')
    -- Convert RetypesExpr into Retypes of a variable.
    doSpecification (A.Specification m n (A.RetypesExpr m' am toT e))
        =  do e' <- doExpression e
              fromT <- astTypeOf e'
              spec@(A.Specification _ n' _) <- makeNonceIsExpr "retypes_expr" m' fromT e'
              addPulled $ (m', Left spec)
              return $ A.Specification m n (A.Retypes m' am toT (A.Variable m' n'))
    doSpecification s = doGeneric s

    -- | Filter what can be pulled in LiteralReprs.
    doLiteralRepr :: A.LiteralRepr -> PassM A.LiteralRepr
    -- FIXME: We could do away with ArrayElem and have a rule like the below
    -- for nested array literals.
    -- Don't pull up array expressions that are fields of record literals.
    doLiteralRepr (A.RecordLiteral m es)
        =  do es' <- mapM (if pullUpArraysInsideRecords then doExpression else doExpression') es    -- note doExpression' rather than pullUp
              return $ A.RecordLiteral m es'
    doLiteralRepr lr = doGeneric lr

    -- | Pull array expressions that aren't already non-subscripted variables.
    -- Also pull lists that are literals or constructed
    doExpression :: A.Expression -> PassM A.Expression
    doExpression e
              -- This part handles recursing into the expression first:
        =  do e' <- doExpression' e
              t <- astTypeOf e'
              case t of
                A.Array _ _ ->
                  case e' of
                    A.ExprVariable _ (A.Variable _ _) -> return e'
                    A.ExprVariable _ (A.DirectedVariable _ _ _) -> return e'
                    --TODO work out whether to pull up DerefVariable
                    _ -> pull t e'
                A.List _ ->
                  case e' of
                    A.ExprConstr {} -> pull t e'
                    A.Literal {} -> pull t e'
                    _ -> return e'
                _ -> return e'
      where
        pull :: A.Type -> A.Expression -> PassM A.Expression
        pull t e
            = do let m = findMeta e
                 spec@(A.Specification _ n _) <- makeNonceIsExpr "array_expr" m t e
                 addPulled $ (m, Left spec)
                 return $ A.ExprVariable m (A.Variable m n)

    -- | Pull any variable subscript that results in an array.
    doVariable :: A.Variable -> PassM A.Variable
    doVariable v@(A.SubscriptedVariable m _ _)
        =  do v' <- doGeneric v
              t <- astTypeOf v'
              case t of
                A.Array _ _ ->
                  do origAM <- abbrevModeOfVariable v'
                     let am = makeAbbrevAM origAM
                     spec@(A.Specification _ n _) <- makeNonceIs "array_slice" m t am v'
                     addPulled $ (m, Left spec)
                     return $ A.Variable m n
                _ -> return v'
    doVariable v = doGeneric v

    -- | Convert a FUNCTION call into some variables and a PROC call.
    convertFuncCall :: Meta -> A.Name -> [A.Expression] -> PassM [A.Variable]
    convertFuncCall m n es
        = do es' <- pullUpRecur es
             ets <- sequence [astTypeOf e | e <- es']

             ps <- get
             rts <- Map.lookup (A.nameName n) (csFunctionReturns ps)
             specs <- sequence [makeNonceVariable "return_actual" m t A.VariableName A.Original | t <- rts]
             sequence_ [addPulled $ (m, Left spec) | spec <- specs]

             let names = [n | A.Specification _ n _ <- specs]
             let vars = [A.Variable m n | n <- names]
             let call = A.ProcCall m n (map A.ActualExpression es' ++ map A.ActualVariable vars)
             addPulled $ (m, Right call)

             return vars

    doExpression' :: A.Expression -> PassM A.Expression
    -- Convert single-valued function calls.
    doExpression' (A.FunctionCall m n es)
        = do [v] <- convertFuncCall m n es
             return $ A.ExprVariable m v
    -- Convert SubscriptedExprs into SubscriptedVariables.
    doExpression' (A.SubscriptedExpr m s e)
        = do e' <- pullUpRecur e
             s' <- pullUpRecur s
             t <- astTypeOf e'
             spec@(A.Specification _ n _) <- makeNonceIsExpr "subscripted_expr" m t e'
             addPulled $ (m, Left spec)
             return $ A.ExprVariable m (A.SubscriptedVariable m s' (A.Variable m n))
    doExpression' e = doGeneric e

    doExpressionList :: A.ExpressionList -> PassM A.ExpressionList
    -- Convert multi-valued function calls.
    doExpressionList (A.FunctionCallList m n es)
        = do vs <- convertFuncCall m n es
             return $ A.ExpressionList m [A.ExprVariable m v | v <- vs]
    doExpressionList el = doGeneric el

