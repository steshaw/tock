{-
Tock: a compiler for parallel languages
Copyright (C) 2007, 2008  University of Kent

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
import Traversal
import Types
import Utils

simplifyExprs :: [Pass]
simplifyExprs =
      [ functionsToProcs
      , removeAfter
      , expandArrayLiterals
      , pullRepCounts
      , pullUp False
      , transformConstr
      ]

-- These are a special case, and do not get pulled up, nor turned into PROCs:
builtInOperatorFunction :: A.Name -> Bool
builtInOperatorFunction = (`elem` occamBuiltInOperatorFunctions) . A.nameName


-- | Convert FUNCTION declarations to PROCs.
functionsToProcs :: Pass
functionsToProcs = pass "Convert FUNCTIONs to PROCs"
  (Prop.agg_namesDone ++ [Prop.expressionTypesChecked, Prop.parUsageChecked,
        Prop.functionTypesChecked])
  [Prop.functionsRemoved]
  (applyDepthM doSpecification)
  where
    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification (A.Specification m n (A.Function mf smrm rts fs evp))
      | not (builtInOperatorFunction n)
        = do -- Create new names for the return values.
             specs <- sequence [makeNonceVariable "return_formal" mf t A.Abbrev | t <- rts]
             let names = [n | A.Specification mf n _ <- specs]
             -- Note the return types so we can fix calls later.
             modify $ (\ps -> ps { csFunctionReturns = Map.insert (A.nameName n) rts (csFunctionReturns ps) })
             -- Turn the value process into an assignment process.
             let p = fmap (vpToSeq m n [A.Variable mf n | n <- names]) evp
             let st = A.Proc mf smrm (fs ++ [A.Formal A.Abbrev t n | (t, n) <- zip rts names]) p
             -- Build a new specification and redefine the function.
             let spec = A.Specification m n st
             let nd = A.NameDef {
                        A.ndMeta = mf,
                        A.ndName = A.nameName n,
                        A.ndOrigName = A.nameName n,
                        A.ndSpecType = st,
                        A.ndAbbrevMode = A.Original,
                        A.ndNameSource = A.NameUser,
                        A.ndPlacement = A.Unplaced
                      }
             defineName n nd
             return spec
    doSpecification s = return s

    vpToSeq :: Meta -> A.Name -> [A.Variable] -> Either (A.Structured A.ExpressionList) A.Process -> A.Process
    vpToSeq m n vs (Left el) = A.Seq m $ vpToSeq' el vs
    vpToSeq _ n vs (Right p) = subst p
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
removeAfter :: Pass
removeAfter = pass "Convert AFTER to MINUS"
  [Prop.expressionTypesChecked]
  [Prop.afterRemoved]
  (applyDepthM2 doExpression doExpressionList)
  where
    doFunctionCall :: (Meta -> A.Name -> [A.Expression] -> a)
      -> Meta -> A.Name -> [A.Expression] -> PassM a
    doFunctionCall f m n args
        =  do mOp <- builtInOperator n
              ts <- mapM astTypeOf args
              let op s = A.Name (A.nameMeta n) $ occamDefaultOperator s ts
              case mOp of
                Just "AFTER"
                  | A.nameName n == occamDefaultOperator "AFTER" [A.Byte, A.Byte] ->
                   let one = A.Literal m A.Byte $ A.IntLiteral m "1"
                       oneTwoSeven = A.Literal m A.Byte $ A.IntLiteral m "127"
                   in        return $ f m (op "<")
                               [A.FunctionCall m (op "MINUS")
                                 [A.FunctionCall m (op "MINUS") args
                                 , one]
                               ,oneTwoSeven]
                  | otherwise
                   -> let zero = A.Literal m (head ts) $ A.IntLiteral m "0"
                      in return $ f m (op ">") [A.FunctionCall m (op "MINUS") args, zero]
                _ -> return $ f m n args

    doExpression :: A.Expression -> PassM A.Expression
    doExpression e@(A.FunctionCall m n args)
        = doFunctionCall A.FunctionCall m n args    
    doExpression e = return e

    doExpressionList :: A.ExpressionList -> PassM A.ExpressionList
    doExpressionList e@(A.FunctionCallList m n args)
        = doFunctionCall A.FunctionCallList m n args    
    doExpressionList e = return e   

-- | For array literals that include other arrays, burst them into their
-- elements.
expandArrayLiterals :: Pass
expandArrayLiterals = pass "Expand array literals"
  [Prop.expressionTypesChecked, Prop.processTypesChecked]
  [Prop.arrayLiteralsExpanded]
  (applyDepthM doArrayElem)
  where
    doArrayElem :: A.Structured A.Expression -> PassM (A.Structured A.Expression)
    doArrayElem ae@(A.Only _ e)
        =  do t <- astTypeOf e
              case (t, e) of
                (A.Array ds _, _) -> expand ds e
                _ -> return ae
    doArrayElem ae = return ae

    expand :: [A.Dimension] -> A.Expression -> PassM (A.Structured A.Expression)
    expand [] e = return $ A.Only (findMeta e) e
    expand (A.UnknownDimension:_) e
        = dieP (findMeta e) "array literal containing non-literal array of unknown size"
    expand (A.Dimension n:ds) e
        =  do -- Because it's an array literal, we must know the size.
              size <- evalIntExpression n
              elems <- sequence [case e of
                         A.Literal _ _ (A.ArrayListLiteral _ (A.Several _ ls)) ->
                           return $ ls !! i
                         _ -> expand ds (A.SubscriptedExpr m
                                             (A.Subscript m A.NoCheck $
                                               makeConstant m i) e)
                                 | i <- [0 .. size - 1]]
              return $ A.Several (findMeta e) elems
      where m = findMeta e

-- | We pull up the loop (Rep) counts into a temporary expression, whenever the loop
-- count could be modified within the loop.  Here are all things that can be replicated:
-- SEQ -- can be altered during the loop, must pull up
-- PAR -- count cannot be modified by code inside the loop (it is used before any PAR branches are run)
--        BUT since we implement replicated pars using a loop that forks off those
--        processes, it seems safest to pull up 
-- IF  -- cannot be altered during loop; once body executes, loop is effectively broken
-- ALT -- same as IF
--        BUT the programmer could offer to read into the replication count, which
--        could cause all sorts of horrendous problems, so pull up
-- Therefore, we only need to pull up the counts for SEQ, PAR and ALT
--
-- TODO for simplification, we could avoid pulling up replication counts that are known to be constants
--
-- TODO we should also pull up the step counts
pullRepCounts :: Pass
pullRepCounts = pass "Pull up replicator counts for SEQs, PARs and ALTs"
  (Prop.agg_namesDone ++ Prop.agg_typesDone)
  []
  (applyDepthM pullRepCountProc)
  where
    pullRepCountStr :: Data a => Bool -> A.Structured a
      -> StateT (A.Structured A.Process -> A.Structured A.Process)
           PassM (A.Structured a)
    pullRepCountStr addHere (A.Spec m (A.Specification mspec n (A.Rep mrep (A.For mfor
      from for step))) scope)
      = do t <- lift $ astTypeOf for
           spec@(A.Specification _ nonceName _) <- lift $ makeNonceIsExpr "rep_for" mspec t for
           let newRepSpec = (A.Rep mrep (A.For mfor from (A.ExprVariable mspec $ A.Variable mspec nonceName) step))
           lift $ modifyName n $ \nd -> nd { A.ndSpecType = newRepSpec }
           if addHere
             then return $ A.Spec mspec spec $
                    A.Spec m (A.Specification mspec n newRepSpec) scope
             else do modify (. A.Spec mspec spec)
                     return $ A.Spec m (A.Specification mspec n newRepSpec) scope
    pullRepCountStr _ s = return s

    pullRepCountProc :: Transform A.Process
    pullRepCountProc (A.Alt m p body) = evalStateT (pullRepCountStr True body) id >>* A.Alt m p
    pullRepCountProc (A.Seq m body) = evalStateT (pullRepCountStr True body) id >>* A.Seq m
    pullRepCountProc (A.Par m p body)
      = do (body', spec) <- runStateT (pullRepCountStr False body) id
           return $ A.Seq m $ spec $ A.Only m $ A.Par m p body'
    pullRepCountProc p = return p

transformConstr :: Pass
transformConstr = pass "Transform array constructors into initialisation code"
  (Prop.agg_namesDone ++ Prop.agg_typesDone ++ [Prop.subscriptsPulledUp])
  [Prop.arrayConstructorsRemoved]
  (applyDepthSM doStructured)
  where
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
    doStructured (A.Spec m (A.Specification m' n (A.Is _ _ _
      (A.ActualExpression expr@(A.Literal m'' t (A.ArrayListLiteral _ (A.Spec _ (A.Specification _
        repn (A.Rep _ rep)) repExp)))))) scope)
      = do case t of
             A.Array {} ->
               do indexVarSpec@(A.Specification _ indexName _) <- makeNonceVariable "array_constr_index" m'' A.Int A.Original
                  let indexVar = A.Variable m'' indexName
                      (repExp', specs) = stripSpecs repExp

                  tInner <- trivialSubscriptType m t

                  -- To avoid confusion in later passes, we must change the abbreviation
                  -- mode for this thing from ValAbbrev (which it must have been)
                  -- to Original, since we are now actually declaring it and assigning
                  -- to it:
                  modifyName n $ \nd -> nd {A.ndAbbrevMode = A.Original}

                  incIndex <- incrementIndex indexVar

                  let body = specs $ A.Several m''
                            [ assignItem tInner indexVar repExp'
                            , incIndex ]
                  body' <- applyDepthSM doStructured body

                  return $ declDest $ A.ProcThen m''
                    (A.Seq m'' $ A.Spec m'' indexVarSpec $
                      A.Several m'' [assignIndex0 indexVar,
                        replicateCode $ body'
                    ])
                    scope
             A.List {} ->
               return $ declDest $ A.ProcThen m''
                 (A.Seq m'' $ replicateCode $ appendItem)
                 scope
             _ -> diePC m $ formatCode "Unsupported type for array constructor: %" t
      where
        -- Also strips ProcThen
        stripSpecs :: A.Structured A.Expression -> (A.Structured A.Expression,
          A.Structured A.Process -> A.Structured A.Process)
        stripSpecs (A.Spec m spec scope)
          = let (result, innerSpecs) = stripSpecs scope in
              (result, A.Spec m spec . innerSpecs)
        stripSpecs (A.ProcThen m proc body)
          = let (result, innerSpecs) = stripSpecs body in
              (result, A.ProcThen m proc . innerSpecs)
        stripSpecs se = (se, id)
        
        declDest :: Data a => A.Structured a -> A.Structured a
        declDest = A.Spec m (A.Specification m' n (A.Declaration m' t))

        assignIndex0 :: A.Variable -> A.Structured A.Process
        assignIndex0 indexVar = A.Only m'' $ A.Assign m'' [indexVar] $
          A.ExpressionList m'' [A.Literal m'' A.Int $ A.IntLiteral m'' "0"]

        incrementIndex :: A.Variable -> PassM (A.Structured A.Process)
        incrementIndex indexVar
          = do indexVar_plus1 <- addOne $ A.ExprVariable m'' indexVar
               return $ A.Only m'' $ A.Assign m'' [indexVar] $ A.ExpressionList m'' [indexVar_plus1]

        assignItem :: A.Type -> A.Variable -> A.Structured A.Expression -> A.Structured A.Process
        assignItem t' indexVar repExp' = A.Only m'' $ A.Assign m'' [A.SubscriptedVariable m''
          (A.Subscript m'' A.NoCheck $ A.ExprVariable m'' indexVar) $
            A.Variable m'' n] $ A.ExpressionList m'' [
              case repExp' of
                A.Only _ e -> e
                _ -> A.Literal m'' t' $ A.ArrayListLiteral m'' repExp'
              ]

        appendItem :: A.Structured A.Process
        appendItem = A.Only m'' $ A.Assign m'' [A.Variable m'' n] $
          A.ExpressionList m'' [A.FunctionCall m'' (A.Name m'' "++")
            [A.ExprVariable m'' $ A.Variable m'' n
            ,A.Literal m'' (let A.List tInner = t in tInner) $ A.ArrayListLiteral m'' repExp
            ]]
            

        replicateCode :: Data a => A.Structured a -> A.Structured a
        replicateCode = A.Spec m'' (A.Specification m'' repn (A.Rep m'' rep))

    doStructured s = return s

-- | Find things that need to be moved up to their enclosing Structured, and do
-- so.
pullUp :: Bool -> Pass
pullUp pullUpArraysInsideRecords = pass "Pull up definitions"
  (Prop.agg_namesDone ++ Prop.agg_typesDone ++ [Prop.functionsRemoved, Prop.seqInputsFlattened])
  [Prop.functionCallsRemoved, Prop.subscriptsPulledUp]
  recurse
  where
    ops :: Ops
    ops = baseOp
          `extOpS` doStructured
          `extOp` doProcess
          `extOp` doRepArray
          `extOp` doSpecification
          `extOp` doLiteralRepr
          `extOp` doExpression
          `extOp` doVariable
          `extOp` doExpressionList
    recurse :: Recurse
    recurse = makeRecurse ops
    descend :: Descend
    descend = makeDescend ops

    -- | When we encounter a Structured, create a new pulled items state,
    -- recurse over it, then apply whatever pulled items we found to it.
    doStructured :: Data a => A.Structured a -> PassM (A.Structured a)
    doStructured s
        =  do pushPullContext
              -- Recurse over the body, then apply the pulled items to it
              s' <- descend s >>= applyPulled
              -- ... and restore the original pulled items
              popPullContext
              return s'

    doProcActual :: Transform A.Actual
    doProcActual a@(A.ActualVariable {}) = descend a
    doProcActual a@(A.ActualExpression {}) = descend a
    -- Definitely pull up channel arrays and claims:
    doProcActual a
        =  do a' <- recurse a
              t <- astTypeOf a
              spec@(A.Specification _ n' _)
                <- defineNonce m "actual" (A.Is m A.Abbrev t a) A.Abbrev
              addPulled (m, Left spec)
              return $ A.ActualVariable (A.Variable m n')
      where
        m = findMeta a

    -- | As with doStructured: when we find a process, create a new pulled items
    -- context, and if we find any items apply them to it.
    doProcess :: A.Process -> PassM A.Process
    doProcess p
        =  do pushPullContext
              p' <- case p of
                A.ProcCall m n as
                  -> mapM doProcActual as >>* A.ProcCall m n
                _ -> descend p
              pulled <- havePulled
              p'' <- if pulled
                       then liftM (A.Seq emptyMeta) $ applyPulled (A.Only emptyMeta p')
                       else return p'
              popPullContext
              return p''

    -- | There are issues with array constructors.  Consider:
    --   [i = 0 FOR 10 | [i, i+1]]
    -- You cannot pull the inner array literal up past the replicator,
    -- because then i will not be in scope.  So what we must do is
    -- pull the array up to just inside the replicator (while pulling the whole
    -- literal up as normal):
    --   VAL array_expr_outer IS [i = 3 FOR 5 |
    --     VAL array_expr_inner IS [i, i + 1]:
    --       array_expr_inner]
    -- Then when it is transformed later, it should become:
    --   array_expr_outer:
    --   PROCTHEN
    --     INT array_constr_index:
    --     SEQ
    --       array_constr_index := 0
    --       SEQ i = 3 FOR 5
    --         VAL array_expr_inner IS [i, i + 1]:
    --         SEQ
    --           array_expr_outer[array_constr_index] := array_expr_inner -- itself flattened later!
    --           array_constr_index := array_constr_index + 1
    doRepArray :: A.Structured A.Expression -> PassM (A.Structured A.Expression)
    doRepArray (A.Spec m spec@(A.Specification _ _ (A.Rep {})) scope)
      = do -- We descend into the spec before we push a new context,
           -- as anything in the spec should be pulled up to the outer context,
           -- not inside the replicator
           spec' <- descend spec
           pushPullContext
           scope' <- recurse scope >>= applyPulled
           popPullContext
           return $ A.Spec m spec' scope'
    doRepArray s = descend s

    -- | Filter what can be pulled in Specifications.
    doSpecification :: A.Specification -> PassM A.Specification
    -- Iss might be SubscriptedVars -- which is fine; the backend can deal with that.
    doSpecification (A.Specification m n (A.Is m' am t (A.ActualVariable v)))
        =  do v' <- descend v    -- note descend rather than pullUp
              return $ A.Specification m n (A.Is m' am t $ A.ActualVariable v')
    -- IsExprs might be SubscriptedExprs, and if so we have to convert them.
    doSpecification (A.Specification m n (A.Is m' am t (A.ActualExpression e)))
        =  do e' <- doExpression' e  -- note doExpression' rather than recurse
              return $ A.Specification m n (A.Is m' am t $ A.ActualExpression e')
    -- Convert RetypesExpr into Retypes of a variable.
    doSpecification (A.Specification m n (A.RetypesExpr m' am toT e))
        =  do e' <- doExpression e
              fromT <- astTypeOf e'
              spec@(A.Specification _ n' _) <- makeNonceIsExpr "retypes_expr" m' fromT e'
              addPulled $ (m', Left spec)
              return $ A.Specification m n (A.Retypes m' am toT (A.Variable m' n'))
    doSpecification s = descend s

    -- | Filter what can be pulled in LiteralReprs.
    doLiteralRepr :: A.LiteralRepr -> PassM A.LiteralRepr
    -- FIXME: We could do away with ArrayElem and have a rule like the below
    -- for nested array literals.
    -- Don't pull up array expressions that are fields of record literals.
    doLiteralRepr (A.RecordLiteral m es)
        =  do es' <- mapM (if pullUpArraysInsideRecords then doExpression else doExpression') es    -- note doExpression' rather than recurse
              return $ A.RecordLiteral m es'
    doLiteralRepr lr = descend lr

    -- | Pull array expressions that aren't already non-subscripted variables.
    -- Also pull lists that are literals or constructed
    doExpression :: A.Expression -> PassM A.Expression
    -- For is-defined, we don't want to pull up:
    doExpression e@(A.IsDefined {}) = return e
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
                    A.Literal {} -> pull t e'
                    _ -> return e'
                A.Record _ ->
                  case e' of
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

    -- | Pull any variable subscript that results in an array, or contains a slice.
    doVariable :: A.Variable -> PassM A.Variable
    doVariable v@(A.SubscriptedVariable m sub _)
        =  do v' <- if isSlice sub then descend v else descendAfterSubscripts v
              t <- astTypeOf v'
              case t of
                A.Array _ _ ->
                  do origAM <- abbrevModeOfVariable v'
                     let am = makeAbbrevAM origAM
                     spec@(A.Specification _ n _) <- makeNonceIs "array_slice" m t am v'
                     addPulled $ (m, Left spec)
                     return $ A.Variable m n
                _ -> return v'
      where
        descendAfterSubscripts (A.SubscriptedVariable m sub v) | not (isSlice sub)
          = do sub' <- recurse sub
               v' <- descendAfterSubscripts v
               return $ A.SubscriptedVariable m sub' v'
        descendAfterSubscripts v = doVariable v

        isSlice (A.SubscriptFromFor {}) = True
        isSlice (A.SubscriptFrom {}) = True
        isSlice (A.SubscriptFor {}) = True
        isSlice _ = False
    doVariable v@(A.DirectedVariable m dir innerV)
      = do t <- astTypeOf innerV
           case t of
             A.Array ds (A.Chan attr innerT) ->
               do let ds' = [case d of
                        A.Dimension {} -> d
                        A.UnknownDimension -> A.Dimension $ A.ExprVariable m $
                          specificDimSize i innerV
                        | (d, i) <- zip ds [0..]]
                  spec@(A.Specification _ n _) <- makeNonceIs "dir_array" m
                    (A.Array ds' $ A.ChanEnd dir (dirAttr dir attr) innerT) A.Abbrev v
                  addPulled $ (m, Left spec)
                  return $ A.Variable m n
             _ -> descend v
    doVariable v@(A.VariableSizes m _)
      = do v' <- descend v
           t <- astTypeOf v'
           spec@(A.Specification _ n _) <- makeNonceIs "sizes_array" m t A.ValAbbrev v'
           addPulled $ (m, Left spec)
           return $ A.Variable m n
    doVariable v = descend v

    -- | Convert a FUNCTION call into some variables and a PROC call.
    convertFuncCall :: Meta -> A.Name -> [A.Expression] -> PassM [A.Variable]
    convertFuncCall m n es
        = do es' <- recurse es
             ets <- sequence [astTypeOf e | e <- es']

             ps <- get
             rts <- case Map.lookup (A.nameName n) (csFunctionReturns ps) of
               Nothing -> dieP m "Could not find function returns"
               Just x -> return x
             specs <- sequence [makeNonceVariable "return_actual" m t A.Original | t <- rts]
             sequence_ [addPulled $ (m, Left spec) | spec <- specs]

             let names = [n | A.Specification _ n _ <- specs]
             let vars = [A.Variable m n | n <- names]
             let call = A.ProcCall m n (map A.ActualExpression es' ++ map A.ActualVariable vars)
             addPulled $ (m, Right call)

             return vars

    doExpression' :: A.Expression -> PassM A.Expression
    -- Convert single-valued function calls.
    doExpression' (A.FunctionCall m n es) | not $ builtInOperatorFunction n
        = do [v] <- convertFuncCall m n es
             return $ A.ExprVariable m v
    -- Convert SubscriptedExprs into SubscriptedVariables.
    doExpression' (A.SubscriptedExpr m s e)
        = do e' <- recurse e
             s' <- recurse s
             t <- astTypeOf e'
             spec@(A.Specification _ n _) <- makeNonceIsExpr "subscripted_expr" m t e'
             addPulled $ (m, Left spec)
             return $ A.ExprVariable m (A.SubscriptedVariable m s' (A.Variable m n))
    doExpression' e = descend e

    doExpressionList :: A.ExpressionList -> PassM A.ExpressionList
    -- Convert multi-valued function calls.
    doExpressionList (A.FunctionCallList m n es)
      | not (builtInOperatorFunction n)
        = do vs <- convertFuncCall m n es
             return $ A.ExpressionList m [A.ExprVariable m v | v <- vs]
    doExpressionList el = descend el

