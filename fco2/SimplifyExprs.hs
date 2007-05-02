-- | Simplify expressions in the AST.
module SimplifyExprs (simplifyExprs) where

import Control.Monad.State
import Data.Generics
import qualified Data.Map as Map
import Data.Maybe

import qualified AST as A
import Errors
import Metadata
import ParseState
import Types
import Pass

simplifyExprs :: A.Process -> PassM A.Process
simplifyExprs = runPasses passes
  where
    passes =
      [ ("Convert FUNCTIONs to PROCs", functionsToProcs)
      , ("Convert AFTER to MINUS", removeAfter)
      , ("Expand array literals", expandArrayLiterals)
      , ("Pull up definitions", pullUp)
      ]

-- | Convert FUNCTION declarations to PROCs.
functionsToProcs :: Data t => t -> PassM t
functionsToProcs = doGeneric `extM` doSpecification
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric functionsToProcs

    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification (A.Specification m n (A.Function mf sm rts fs vp))
        = do -- Create new names for the return values.
             specs <- sequence [makeNonceVariable "return_formal" mf t A.VariableName A.Abbrev | t <- rts]
             let names = [n | A.Specification mf n _ <- specs]
             -- Note the return types so we can fix calls later.
             modify $ (\ps -> ps { psFunctionReturns = Map.insert (A.nameName n) rts (psFunctionReturns ps) })
             -- Turn the value process into an assignment process.
             let p = A.Seq mf $ vpToSeq vp [A.Variable mf n | n <- names]
             let st = A.Proc mf sm (fs ++ [A.Formal A.Abbrev t n | (t, n) <- zip rts names]) p
             -- Build a new specification and redefine the function.
             let spec = A.Specification m n st
             let nd = A.NameDef {
                        A.ndMeta = mf,
                        A.ndName = A.nameName n,
                        A.ndOrigName = A.nameName n,
                        A.ndNameType = A.ProcName,
                        A.ndType = st,
                        A.ndAbbrevMode = A.Original,
                        A.ndPlacement = A.Unplaced
                      }
             defineName n nd
             doGeneric spec
    doSpecification s = doGeneric s

    vpToSeq :: A.Structured -> [A.Variable] -> A.Structured
    vpToSeq (A.Spec m spec s) vs = A.Spec m spec (vpToSeq s vs)
    vpToSeq (A.ProcThen m p s) vs = A.ProcThen m p (vpToSeq s vs)
    vpToSeq (A.OnlyEL m el) vs = A.OnlyP m $ A.Assign m vs el

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
              t <- typeOfExpression a'
              let zero = A.Literal m t $ A.IntLiteral m "0"
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
              t <- typeOfExpression e'
              case t of
                A.Array ds _ -> expand ds e
                _ -> doGeneric ae
    doArrayElem ae = doGeneric ae

    expand :: [A.Dimension] -> A.Expression -> PassM A.ArrayElem
    expand [] e = return $ A.ArrayElemExpr e
    expand (A.UnknownDimension:_) _
        = die "array literal containing non-literal array of unknown size"
    expand (A.Dimension n:ds) e
        = liftM A.ArrayElemArray $ sequence [expand ds (A.SubscriptedExpr m (A.Subscript m $ makeConstant m i) e) | i <- [0 .. (n - 1)]]
      where m = findMeta e

-- | Find things that need to be moved up to their enclosing Structured, and do
-- so.
pullUp :: Data t => t -> PassM t
pullUp = doGeneric `extM` doStructured `extM` doProcess `extM` doSpecification `extM` doExpression `extM` doVariable `extM` doExpressionList
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric pullUp

    -- | When we encounter a Structured, create a new pulled items state,
    -- recurse over it, then apply whatever pulled items we found to it.
    doStructured :: A.Structured -> PassM A.Structured
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
                       then liftM (A.Seq emptyMeta) $ applyPulled (A.OnlyP emptyMeta p')
                       else return p'
              popPullContext
              return p''

    -- | *Don't* pull anything that's already an abbreviation -- but do convert
    -- RetypesExpr into Retypes (of a variable).
    doSpecification :: A.Specification -> PassM A.Specification
    -- Iss might be SubscriptedVars -- which is fine; the backend can deal with that.
    doSpecification (A.Specification m n (A.Is m' am t v))
        =  do v' <- doGeneric v    -- note doGeneric rather than pullUp
              return $ A.Specification m n (A.Is m' am t v')
    -- IsExprs might be SubscriptedExprs, and if so we have to convert them.
    doSpecification (A.Specification m n (A.IsExpr m' am t e))
        =  do e' <- doExpression' e  -- note doExpression' rather than pullUp
              return $ A.Specification m n (A.IsExpr m' am t e')
    doSpecification (A.Specification m n (A.RetypesExpr m' am toT e))
        =  do e' <- doExpression e
              fromT <- typeOfExpression e'
              spec@(A.Specification _ n' _) <- makeNonceIsExpr "retypes_expr" m' fromT e'
              addPulled $ A.Spec m' spec
              return $ A.Specification m n (A.Retypes m' am toT (A.Variable m' n'))
    doSpecification s = doGeneric s

    -- | Pull array expressions that aren't already non-subscripted variables.
    doExpression :: A.Expression -> PassM A.Expression
    doExpression e
        =  do e' <- doExpression' e
              t <- typeOfExpression e'
              case t of
                A.Array _ _ ->
                  case e' of
                    A.ExprVariable _ (A.Variable _ _) -> return e'
                    _ -> pull t e'
                _ -> return e'
      where
        pull :: A.Type -> A.Expression -> PassM A.Expression
        pull t e
            = do let m = findMeta e
                 spec@(A.Specification _ n _) <- makeNonceIsExpr "array_expr" m t e
                 addPulled $ A.Spec m spec
                 return $ A.ExprVariable m (A.Variable m n)

    -- | Pull any variable subscript that results in an array.
    doVariable :: A.Variable -> PassM A.Variable
    doVariable v@(A.SubscriptedVariable m _ _)
        =  do v' <- doGeneric v
              t <- typeOfVariable v'
              case t of
                A.Array _ _ ->
                  do origAM <- abbrevModeOfVariable v'
                     let am = makeAbbrevAM origAM
                     spec@(A.Specification _ n _) <- makeNonceIs "array_slice" m t am v'
                     addPulled $ A.Spec m spec
                     return $ A.Variable m n
                _ -> return v'
    doVariable v = doGeneric v

    -- | Convert a FUNCTION call into some variables and a PROC call.
    convertFuncCall :: Meta -> A.Name -> [A.Expression] -> PassM [A.Variable]
    convertFuncCall m n es
        = do es' <- pullUp es
             ets <- sequence [typeOfExpression e | e <- es']

             ps <- get
             rts <- Map.lookup (A.nameName n) (psFunctionReturns ps)
             specs <- sequence [makeNonceVariable "return_actual" m t A.VariableName A.Original | t <- rts]
             sequence_ [addPulled $ A.Spec m spec | spec <- specs]

             let names = [n | A.Specification _ n _ <- specs]
             let vars = [A.Variable m n | n <- names]
             let call = A.ProcCall m n ([A.ActualExpression t e | (t, e) <- zip ets es'] ++ [A.ActualVariable A.Abbrev t v | (t, v) <- zip rts vars])
             addPulled $ A.ProcThen m call

             return vars

    doExpression' :: A.Expression -> PassM A.Expression
    -- Convert single-valued function calls.
    doExpression' (A.FunctionCall m n es)
        = do [v] <- convertFuncCall m n es
             return $ A.ExprVariable m v
    -- Convert SubscriptedExprs into SubscriptedVariables.
    doExpression' (A.SubscriptedExpr m s e)
        = do e' <- pullUp e
             s' <- pullUp s
             t <- typeOfExpression e'
             spec@(A.Specification _ n _) <- makeNonceIsExpr "subscripted_expr" m t e'
             addPulled $ A.Spec m spec
             return $ A.ExprVariable m (A.SubscriptedVariable m s' (A.Variable m n))
    doExpression' e = doGeneric e

    doExpressionList :: A.ExpressionList -> PassM A.ExpressionList
    -- Convert multi-valued function calls.
    doExpressionList (A.FunctionCallList m n es)
        = do vs <- convertFuncCall m n es
             return $ A.ExpressionList m [A.ExprVariable m v | v <- vs]
    doExpressionList el = doGeneric el

