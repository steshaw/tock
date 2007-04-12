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
pullUp = doGeneric `extM` doProcess `extM` doExpression
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
                 spec@(n, _) <- makeNonceValIs m t e
                 addPulled $ A.ProcSpec m spec
                 return $ A.ExprVariable m (A.Variable m n)

