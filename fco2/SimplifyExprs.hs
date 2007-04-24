-- | Simplify expressions in the AST.
module SimplifyExprs (simplifyExprs) where

import Control.Monad.State
import Data.Generics
import Data.Maybe

import qualified AST as A
import Metadata
import ParseState
import Types
import Pass

simplifyExprs :: A.Process -> PassM A.Process
simplifyExprs = runPasses passes
  where
    passes =
      [ ("Convert FUNCTIONs to PROCs", functionsToProcs)
      , ("Pull up definitions", pullUp)
      ]

-- | Convert FUNCTION declarations to PROCs.
functionsToProcs :: Data t => t -> PassM t
functionsToProcs = doGeneric `extM` doSpecification
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapM functionsToProcs

    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification (A.Specification m n (A.Function mf rts fs vp))
        = do -- Create new names for the return values.
             specs <- sequence [makeNonceVariable "return_formal" mf t A.VariableName A.Abbrev | t <- rts]
             let names = [n | A.Specification mf n _ <- specs]
             -- Note the return types so we can fix calls later.
             modify $ (\ps -> ps { psFunctionReturns = (A.nameName n, rts) : psFunctionReturns ps })
             -- Turn the value process into an assignment process.
             let p = vpToProc vp [A.Variable mf n | n <- names]
             let st = A.Proc mf (fs ++ [A.Formal A.Abbrev t n | (t, n) <- zip rts names]) p
             -- Build a new specification and redefine the function.
             let spec = A.Specification m n st
             let nd = A.NameDef {
                        A.ndMeta = mf,
                        A.ndName = A.nameName n,
                        A.ndOrigName = A.nameName n,
                        A.ndNameType = A.ProcName,
                        A.ndType = st,
                        A.ndAbbrevMode = A.Original
                      }
             defineName n nd
             doGeneric spec
    doSpecification s = doGeneric s

    vpToProc :: A.ValueProcess -> [A.Variable] -> A.Process
    vpToProc (A.ValOfSpec m s vp) vs = A.ProcSpec m s (vpToProc vp vs)
    vpToProc (A.ValOf m p el) vs = A.Seq m [p, A.Assign m vs el]

-- | Find things that need to be moved up to their enclosing process, and do
-- so.
pullUp :: Data t => t -> PassM t
pullUp = doGeneric `extM` doProcess `extM` doSpecification `extM` doExpression `extM` doVariable `extM` doExpressionList
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = gmapM pullUp

    -- | When we encounter a process, create a new pulled items state,
    -- recurse over it, then apply whatever pulled items we found to it.
    doProcess :: A.Process -> PassM A.Process
    doProcess p
        =  do -- Save the pulled items
              origPS <- get
              modify (\ps -> ps { psPulledItems = [] })
              -- Recurse over the process, then apply the pulled items to it
              p' <- doGeneric p >>= applyPulled
              -- ... and restore the original pulled items
              modify (\ps -> ps { psPulledItems = psPulledItems origPS })
              return p'

    -- | *Don't* pull anything that's already an abbreviation.
    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification (A.Specification m n (A.Is m' am t v))
        =  do v' <- doGeneric v    -- note doGeneric rather than pullUp
              return $ A.Specification m n (A.Is m' am t v')
    doSpecification (A.Specification m n (A.IsExpr m' am t e))
        =  do e' <- doGeneric e    -- note doGeneric rather than pullUp
              return $ A.Specification m n (A.IsExpr m' am t e')
    doSpecification s = doGeneric s

    -- | Pull array expressions that aren't already non-subscripted variables.
    doExpression :: A.Expression -> PassM A.Expression
    doExpression e
        =  do e' <- doExpressionFunc e
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
            = do let m = metaOfExpression e
                 spec@(A.Specification _ n _) <- makeNonceIsExpr "array_expr" m t e
                 addPulled $ A.ProcSpec m spec
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
                     addPulled $ A.ProcSpec m spec
                     return $ A.Variable m n
                _ -> return v'
    doVariable v = doGeneric v

    -- | Convert a FUNCTION call into some variables and a PROC call.
    convertFuncCall :: Meta -> A.Name -> [A.Expression] -> PassM [A.Variable]
    convertFuncCall m n es
        = do es' <- pullUp es
             ets <- sequence [typeOfExpression e | e <- es']

             ps <- get
             let rts = fromJust $ lookup (A.nameName n) (psFunctionReturns ps)
             specs <- sequence [makeNonceVariable "return_actual" m t A.VariableName A.Original | t <- rts]
             sequence_ [addPulled $ A.ProcSpec m spec | spec <- specs]

             let names = [n | A.Specification _ n _ <- specs]
             let vars = [A.Variable m n | n <- names]
             let call = A.ProcCall m n ([A.ActualExpression t e | (t, e) <- zip ets es'] ++ [A.ActualVariable A.Abbrev t v | (t, v) <- zip rts vars])
             addPulled (\p -> A.Seq m [call, p])

             return vars

    doExpressionFunc :: A.Expression -> PassM A.Expression
    doExpressionFunc (A.FunctionCall m n es)
        = do [v] <- convertFuncCall m n es
             return $ A.ExprVariable m v
    doExpressionFunc e = doGeneric e

    doExpressionList :: A.ExpressionList -> PassM A.ExpressionList
    doExpressionList (A.FunctionCallList m n es)
        = do vs <- convertFuncCall m n es
             return $ A.ExpressionList m [A.ExprVariable m v | v <- vs]
    doExpressionList el = doGeneric el

