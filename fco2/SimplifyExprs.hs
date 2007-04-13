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
simplifyExprs = pullUp

-- | Find things that need to be moved up to their enclosing process, and do
-- so.
pullUp :: Data t => t -> PassM t
pullUp = doGeneric `extM` doProcess `extM` doExpression `extM` doActual
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

    -- | Pull array expressions that aren't already variables.
    doExpression :: A.Expression -> PassM A.Expression
    doExpression e
        =  do e' <- doGeneric e
              ps <- get
              let t = fromJust $ typeOfExpression ps e'
              case t of
                A.Array _ _ ->
                  case e of
                    A.ExprVariable _ _ -> return e'
                    _ -> pull t e'
                _ -> return e'
      where
        pull :: A.Type -> A.Expression -> PassM A.Expression
        pull t e
            = do -- FIXME Should get Meta from somewhere...
                 let m = []
                 spec@(n, _) <- makeNonceIsExpr m t e
                 addPulled $ A.ProcSpec m spec
                 return $ A.ExprVariable m (A.Variable m n)

    -- | Pull array actual slices.
    doActual :: A.Actual -> PassM A.Actual
    doActual a@(A.ActualVariable _ _ _)
        =  do a' <- doGeneric a
              let (am, t, v) = case a' of A.ActualVariable am t v -> (am, t, v)
              case v of
                A.SubscriptedVariable m s _ ->
                  if isSliceSubscript s
                    then do v' <- pull m am t v
                            return $ A.ActualVariable am t v'
                    else return a'
                _ -> return a'
      where
        pull :: Meta -> A.AbbrevMode -> A.Type -> A.Variable -> PassM A.Variable
        pull m am t v
            = do spec@(n, _) <- makeNonceIs m t am v
                 addPulled $ A.ProcSpec m spec
                 return $ A.Variable m n
    doActual a = doGeneric a

