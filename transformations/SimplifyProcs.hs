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

-- | Simplify processes.
module SimplifyProcs (simplifyProcs) where

import Control.Monad.State
import Data.Generics

import qualified AST as A
import CompState
import Metadata
import Types
import Pass

simplifyProcs :: [Pass]
simplifyProcs = makePasses
      [ ("Wrap PAR subprocesses in PROCs", parsToProcs)
      , ("Remove parallel assignment", removeParAssign)
      , ("Flatten assignment", flattenAssign)
      ]

-- | Wrap the subprocesses of PARs in no-arg PROCs.
parsToProcs :: Data t => t -> PassM t
parsToProcs = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric parsToProcs

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Par m pm s)
        =  do s' <- doStructured s
              return $ A.Par m pm s'
    doProcess p = doGeneric p

    -- FIXME This should be generic and in Pass.
    doStructured :: A.Structured A.Process -> PassM (A.Structured A.Process)
    doStructured (A.Rep m r s)
        =  do r' <- parsToProcs r
              s' <- doStructured s
              return $ A.Rep m r' s'
    doStructured (A.Spec m spec s)
        =  do spec' <- parsToProcs spec
              s' <- doStructured s
              return $ A.Spec m spec' s'
    doStructured (A.ProcThen m p s)
        =  do p' <- parsToProcs p
              s' <- doStructured s
              return $ A.ProcThen m p' s'
    doStructured (A.Only m p)
        =  do p' <- parsToProcs p
              s@(A.Specification _ n _) <- makeNonceProc m p'
              return $ A.Spec m s (A.Only m (A.ProcCall m n []))
    doStructured (A.Several m ss)
        = liftM (A.Several m) $ mapM doStructured ss

-- | Turn parallel assignment into multiple single assignments through temporaries.
removeParAssign :: Data t => t -> PassM t
removeParAssign = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric removeParAssign

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Assign m vs@(_:_:_) (A.ExpressionList _ es))
        =  do ts <- mapM typeOfVariable vs
              specs <- sequence [makeNonceVariable "assign_temp" m t A.VariableName A.Original | t <- ts]
              let temps = [A.Variable m n | A.Specification _ n _ <- specs]
              let first = [A.Assign m [v] (A.ExpressionList m [e]) | (v, e) <- zip temps es]
              let second = [A.Assign m [v] (A.ExpressionList m [A.ExprVariable m v']) | (v, v') <- zip vs temps]
              return $ A.Seq m $ foldl (\s spec -> A.Spec m spec s) (A.Several m (map (A.Only m) (first ++ second))) specs
    doProcess p = doGeneric p

-- | Turn assignment of arrays and records into multiple assignments.
flattenAssign :: Data t => t -> PassM t
flattenAssign = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric flattenAssign

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Assign m [v] (A.ExpressionList m' [e]))
        =  do t <- typeOfVariable v
              assign m t v m' e
    doProcess p = doGeneric p

    assign :: Meta -> A.Type -> A.Variable -> Meta -> A.Expression -> PassM A.Process
    assign m t@(A.Array _ _) v m' e = complexAssign m t v m' e
    assign m t@(A.Record _) v m' e = complexAssign m t v m' e
    assign m _ v m' e = return $ A.Assign m [v] (A.ExpressionList m' [e])

    complexAssign :: Meta -> A.Type -> A.Variable -> Meta -> A.Expression -> PassM A.Process
    complexAssign m t v m' e
     = do -- Abbreviate the source and destination, to avoid doing the
          -- subscript each time.
          destAM <- liftM makeAbbrevAM $ abbrevModeOfVariable v
          dest@(A.Specification _ destN _) <-
            makeNonceIs "assign_dest" m t destAM v
          let destV = A.Variable m destN
          src@(A.Specification _ srcN _) <-
            makeNonceIsExpr "assign_src" m' t e
          let srcV = A.Variable m' srcN

          body <- case t of
                    A.Array _ _ ->
                      -- Array assignments become a loop with an assignment
                      -- inside.
                      do counter <- makeNonceCounter "i" m
                         let zero = A.Literal m A.Int $ A.IntLiteral m "0"
                         let rep = A.For m counter zero
                                                   (A.SizeVariable m srcV)
                         itemT <- trivialSubscriptType m t
                         let sub = A.Subscript m (A.ExprVariable m
                                                   (A.Variable m counter))
                         inner <- assign m itemT
                                         (A.SubscriptedVariable m sub destV) m'
                                         (A.ExprVariable m'
                                           (A.SubscriptedVariable m' sub srcV))
                         return $ A.Rep m rep $ A.Only m inner
                    A.Record _ ->
                      -- Record assignments become a sequence of
                      -- assignments, one for each field.
                      do 
                         fs <- recordFields m t
                         assigns <-
                           sequence [do let sub = A.SubscriptField m fName
                                        assign m fType
                                          (A.SubscriptedVariable m sub destV) m'
                                          (A.ExprVariable m'
                                            (A.SubscriptedVariable m' sub srcV))
                                     | (fName, fType) <- fs]
                         return $ A.Several m $ map (A.Only m) assigns

          return $ A.Seq m $ A.Spec m src $ A.Spec m dest body

