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

-- | Simplify processes.
module SimplifyProcs (simplifyProcs) where

import Control.Monad.State
import Data.Generics
import qualified Data.Set as Set

import qualified AST as A
import CompState
import Metadata
import Pass
import qualified Properties as Prop
import Traversal
import Types

simplifyProcs :: [Pass]
simplifyProcs =
      [ parsToProcs
      , removeParAssign
      , flattenAssign
      ]

-- | Wrap the subprocesses of PARs in no-arg PROCs.
parsToProcs :: Pass
parsToProcs = pass "Wrap PAR subprocesses in PROCs"
  [Prop.parUsageChecked]
  [Prop.parsWrapped]
  (applyDepthM doProcess)
  where
    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Par m pm s)
        =  do s' <- doStructured s
              return $ A.Par m pm s'
    doProcess p = return p

    -- FIXME This should be generic and in Pass.
    doStructured :: A.Structured A.Process -> PassM (A.Structured A.Process)
    doStructured = transformOnly wrapProcess
      where
        wrapProcess m p
          =  do s@(A.Specification _ n _) <- makeNonceProc m p
                modify (\cs -> cs { csParProcs = Set.insert n (csParProcs cs) })
                return $ A.Spec m s (A.Only m (A.ProcCall m n []))

-- | Turn parallel assignment into multiple single assignments through temporaries.
removeParAssign :: Pass
removeParAssign = pass "Remove parallel assignment"
  [Prop.parUsageChecked, Prop.functionsRemoved, Prop.functionCallsRemoved]
  [Prop.assignParRemoved]
  (applyDepthM doProcess)
  where
    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Assign m vs@(_:_:_) (A.ExpressionList _ es))
        =  do ts <- mapM astTypeOf vs
              specs <- sequence [makeNonceVariable "assign_temp" m t A.Original | t <- ts]
              let temps = [A.Variable m n | A.Specification _ n _ <- specs]
              let first = [A.Assign m [v] (A.ExpressionList m [e]) | (v, e) <- zip temps es]
              let second = [A.Assign m [v] (A.ExpressionList m [A.ExprVariable m v']) | (v, v') <- zip vs temps]
              return $ A.Seq m $ foldl (\s spec -> A.Spec m spec s) (A.Several m (map (A.Only m) (first ++ second))) specs
    doProcess p = return p

-- | Turn assignment of arrays and records into multiple assignments.
flattenAssign :: Pass
flattenAssign = pass "Flatten assignment"
  (Prop.agg_typesDone ++ [Prop.assignParRemoved])
  [Prop.assignFlattened]
  (makeRecurse ops)
  where
    ops :: Ops
    ops = extOpD (extOpSD baseOp ops doStructured) ops doProcess

    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Assign m [v] (A.ExpressionList m' [e]))
        =  do t <- astTypeOf v
              assign m t v m' e
    doProcess p = return p

    doStructured :: Data a => A.Structured a -> PassM (A.Structured a)
    doStructured (A.Spec m (A.Specification m' n t@(A.RecordType _ _ fs)) s)
      = do procSpec <- recordCopyProc n m fs
           return $ A.Spec m (A.Specification m' n t) (procSpec s)
    doStructured s = return s

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
                         let rep = A.For m zero (A.SizeVariable m srcV) (makeConstant m 1)
                         itemT <- trivialSubscriptType m t
                         -- Don't need to check bounds, as we'll always be within bounds
                         let sub = A.Subscript m A.NoCheck (A.ExprVariable m
                                                   (A.Variable m counter))
                         inner <- assign m itemT
                                         (A.SubscriptedVariable m sub destV) m'
                                         (A.ExprVariable m'
                                           (A.SubscriptedVariable m' sub srcV))
                         return $ A.Spec m (A.Specification m counter (A.Rep m rep)) $ A.Only m inner
                    A.Record n ->
                      return $ A.Only m $ A.ProcCall m (n {A.nameName = "copy_" ++ A.nameName n})
                        [A.ActualVariable destV, A.ActualVariable srcV]

          return $ A.Seq m $ A.Spec m src $ A.Spec m dest body

    -- TODO could make this a separate pass if we wanted (to be run first)
    recordCopyProc :: Data a => A.Name -> Meta -> [(A.Name, A.Type)] -> PassM (A.Structured a -> A.Structured a)
    recordCopyProc n m fs
                      -- Record assignments become a sequence of
                      -- assignments, one for each field.
                    = do let t = A.Record n
                         (A.Specification _ nonceLHS _) <- makeNonceVariable "record_copy_arg" m t A.Abbrev
                         let destV = A.Variable m nonceLHS
                         (A.Specification _ nonceRHS _) <- makeNonceVariable "record_copy_arg" m t A.Abbrev
                         let srcV = A.Variable m nonceRHS
                         assigns <-
                           sequence [do let sub = A.SubscriptField m fName
                                        assign m fType
                                          (A.SubscriptedVariable m sub destV) m
                                          (A.ExprVariable m
                                            (A.SubscriptedVariable m sub srcV))
                                     | (fName, fType) <- fs]
                         let code = A.Seq m $ A.Several m $ map (A.Only m) assigns
                             n' = n {A.nameName = "copy_" ++ A.nameName n}
                             proc = A.Proc m (A.InlineSpec, A.PlainRec)
                                      [A.Formal A.Abbrev t nonceLHS, A.Formal A.ValAbbrev t nonceRHS]
                                      code
                         defineName n' $ A.NameDef {
                           A.ndMeta = m,
                           A.ndName = A.nameName n',
                           A.ndOrigName = A.nameName n',
                           A.ndSpecType = proc,
                           A.ndAbbrevMode = A.Original,
                           A.ndNameSource = A.NameNonce,
                           A.ndPlacement = A.Unplaced
                           }
                           
                         
                         return (A.Spec m (A.Specification m n' proc))
