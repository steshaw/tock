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
module SimplifyProcs (simplifyProcs, fixLowReplicators) where

import Control.Monad.State
import Data.Generics (Data)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import qualified AST as A
import CompState
import EvalConstants
import EvalLiterals
import Metadata
import Pass
import qualified Properties as Prop
import Traversal
import Types
import Utils

simplifyProcs :: [Pass A.AST]
simplifyProcs =
      [ addForkNames
      , parsToProcs
      , removeParAssign
      , flattenAssign
      ]

type ForkM = StateT [A.Name] PassM
type ForkOps = ExtOpM ForkM (ExtOpMS ForkM BaseOp) A.Process

-- | Add an extra barrier parameter to every PROC for FORKING
addForkNames :: PassOnOpsM ForkM ForkOps
addForkNames = occamOnlyPass "Add FORK labels" [] []
  (flip evalStateT [] . recurse)
  where
    ops :: ForkOps
    ops = baseOp `extOpMS` (ops, doStructured) `extOpM` doProcess

    recurse :: RecurseM ForkM ForkOps
    recurse = makeRecurseM ops
    descend :: DescendM ForkM ForkOps
    descend = makeDescendM ops

    doProcess :: A.Process -> ForkM A.Process
    doProcess (A.Fork m Nothing p)
      = do (f:_) <- get
           p' <- recurse p
           return $ A.Fork m (Just f) $ A.Seq m $ A.Several m
             $ map (A.Only m) [p', A.ClearMobile m (A.Variable m f)]
    doProcess p@(A.ProcCall m n as)
      = do (f:_) <- get
           exts <- lift getCompState >>* csExternals
           case lookup (A.nameName n) exts of
             Just ExternalOldStyle -> return p
             _ -> return $ A.ProcCall m n (A.ActualVariable (A.Variable m f) : as)
    doProcess p = descend p

    doStructured :: TransformStructuredM' ForkM ForkOps
    doStructured (A.Spec m spec@(A.Specification _ n (A.Forking _)) scope)
      = do modify (n:)
           scope' <- recurse scope
           modify tail
           return $ A.Spec m spec scope'
    doStructured (A.Spec m (A.Specification m' n spec@(A.Proc m'' smrm fs mbody)) scope)
      = do cs <- lift getCompState
           if csHasMain (csOpts cs) && Just n == listToMaybe (map (fst . snd) (csMainLocals cs))
             then do scope' <- recurse scope
                     mbody' <- case mbody of
                       Nothing -> return Nothing
                       Just body -> do fspec@(A.Specification _ fn _) <- lift $
                                         defineNonce m'' "tlp_forking" (A.Forking m'') A.Original
                                       modify (fn:)
                                       body' <- recurse body
                                       modify tail
                                       return $ Just (A.Seq m'' $ A.Spec m'' fspec
                                         $ A.Only m'' body')
                     return $ A.Spec m (A.Specification m' n (A.Proc m'' smrm fs
                       mbody')) scope'
             else do A.Specification _ fn _ <- lift $ defineNonce m'' "fork_param" (A.Declaration m'' A.Barrier) A.Abbrev
                     modify (fn:)
                     mbody' <- recurse mbody
                     modify tail
                     let fs' = A.Formal A.Abbrev A.Barrier fn : fs
                         alteredSpec = A.Proc m'' smrm fs' mbody'
                     exts <- lift getCompState >>* csExternals
                     spec' <- case lookup (A.nameName n) exts of
                       Just ExternalOldStyle -> return spec
                       _ -> do lift $ modifyName n $ \nd -> nd {A.ndSpecType = alteredSpec}
                               return alteredSpec
                     scope' <- recurse scope
                     return $ A.Spec m (A.Specification m' n spec') scope'
    doStructured s = descend s


-- | Wrap the subprocesses of PARs in no-arg PROCs.
parsToProcs :: PassOn A.Process
parsToProcs = pass "Wrap PAR subprocesses in PROCs"
  [Prop.parUsageChecked]
  [Prop.parsWrapped]
  (applyBottomUpM doProcess)
  where
    doProcess :: A.Process -> PassM A.Process
    doProcess (A.Par m pm s)
        =  do s' <- doStructured s
              return $ A.Par m pm s'
    doProcess (A.Fork m n p)
        =  wrapProcess (A.Fork m n, ForkWrapper) m p >>* A.Seq m
    doProcess p = return p

    -- FIXME This should be generic and in Pass.
    doStructured :: A.Structured A.Process -> PassM (A.Structured A.Process)
    doStructured = transformOnly (wrapProcess (id, ParWrapper))

    wrapProcess (wrap, ty) m p
          =  do s@(A.Specification _ n _) <- makeNonceProc m p
                modify (\cs -> cs { csParProcs = Map.insert n ty (csParProcs cs) })
                return $ A.Spec m s (A.Only m (wrap $ A.ProcCall m n []))

-- | Turn parallel assignment into multiple single assignments through temporaries.
removeParAssign :: PassOn A.Process
removeParAssign = pass "Remove parallel assignment"
  [Prop.parUsageChecked, Prop.functionsRemoved, Prop.functionCallsRemoved]
  [Prop.assignParRemoved]
  (applyBottomUpM doProcess)
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
flattenAssign :: PassOnOps (ExtOpMSP BaseOp `ExtOpMP` A.Process)
flattenAssign = pass "Flatten assignment"
  (Prop.agg_typesDone ++ [Prop.assignParRemoved])
  [Prop.assignFlattened]
  (makeRecurseM ops)
  where
    ops = baseOp `extOpMS` (ops, makeBottomUpM ops doStructured)
                 `extOpM` makeBottomUpM ops doProcess

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

    makeCopyProcName :: A.Name -> PassM A.Name
    makeCopyProcName n = do hash <- getCompState >>* csCompilationHash
                            return $ n {A.nameName = "copy_" ++ hash ++ A.nameName n}

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
                    A.Array (d:_) _ ->
                      -- Array assignments become a loop with an assignment
                      -- inside.
                      do counter <- makeNonceCounter "i" m
                         let zero = A.Literal m A.Int $ A.IntLiteral m "0"
                             limit = case d of
                               A.UnknownDimension -> A.ExprVariable m $ specificDimSize 0 srcV
                               A.Dimension e -> e
                             rep = A.For m zero limit (makeConstant m 1)
                         itemT <- trivialSubscriptType m t
                         -- Don't need to check bounds, as we'll always be within bounds
                         let sub = A.Subscript m A.NoCheck (A.ExprVariable m
                                                   (A.Variable m counter))
                         inner <- assign m itemT
                                         (A.SubscriptedVariable m sub destV) m'
                                         (A.ExprVariable m'
                                           (A.SubscriptedVariable m' sub srcV))
                         return $ A.Spec m (A.Specification m counter (A.Rep m rep)) $ A.Only m inner
                    A.Record n -> makeCopyProcName n >>= \n' ->
                      return $ A.Only m $ A.ProcCall m n'
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
                         (A.Specification _ nonceRHS _) <- makeNonceVariable "record_copy_arg" m t A.ValAbbrev
                         let srcV = A.Variable m nonceRHS
                         assigns <-
                           sequence [do let sub = A.SubscriptField m fName
                                        assign m fType
                                          (A.SubscriptedVariable m sub destV) m
                                          (A.ExprVariable m
                                            (A.SubscriptedVariable m sub srcV))
                                     | (fName, fType) <- fs]
                         n' <- makeCopyProcName n
                         let code = A.Seq m $ A.Several m $ map (A.Only m) assigns
                             proc = A.Proc m (A.InlineSpec, A.PlainRec)
                                      [A.Formal A.Abbrev t nonceLHS, A.Formal A.ValAbbrev t nonceRHS]
                                      (Just code)
                         defineName n' $ A.NameDef {
                           A.ndMeta = m,
                           A.ndName = A.nameName n',
                           A.ndOrigName = A.nameName n',
                           A.ndSpecType = proc,
                           A.ndAbbrevMode = A.Original,
                           A.ndNameSource = A.NameNonce,
                           A.ndPlacement = A.Unplaced
                           }

                         modifyCompState $ \cs ->
                           if A.nameName n `elem` csOriginalTopLevelProcs cs
                             then cs { csOriginalTopLevelProcs = A.nameName n' : csOriginalTopLevelProcs cs}
                             else cs
                         
                         return (A.Spec m (A.Specification m n' proc))

-- | Removes replicators with a replicator count of zero,
-- and transforms replicators with a replicator count of one.
--
-- We don't currently transform replicators in array constructors,
-- just replicators in SEQ, PAR, ALT, IF.
--
-- This pass is primarily to make sure that PAR replicators with 0 or 1 counts
-- pass the usage checking, but it doesn't hurt to remove any redundant code (or
-- simplify code) in the other replicators.
fixLowReplicators :: PassOn A.Process
fixLowReplicators = pass "Fix low-count (0, 1) replicators" [] []
  (applyBottomUpM doProcess)
  where
    doProcess :: Transform A.Process
    doProcess (A.Seq m s) = doStructured s >>* A.Seq m
    doProcess (A.Par m p s) = doStructured s >>* A.Par m p
    doProcess (A.If m s) = doStructured s >>* A.If m
    doProcess (A.Alt m p s) = doStructured s >>* A.Alt m p
    doProcess p = return p

    doStructured :: Data a => Transform (A.Structured a)
    doStructured s@(A.Only {}) = return s
    doStructured (A.Several m ss) = mapM doStructured ss >>* A.Several m
    doStructured (A.ProcThen m p s) = doStructured s >>* A.ProcThen m p
    doStructured (A.Spec m sp@(A.Specification m' n (A.Rep m''
      (A.For m''' begin end _))) s)
      | isConstant end
      = do endVal <- evalIntExpression end
           case endVal of
             0 -> return $ A.Several m []
             1 -> doStructured s >>*
                    A.Spec m (A.Specification m' n
                      (A.Is m'' A.ValAbbrev A.Int $ A.ActualExpression begin)) 
             _ -> doStructured s >>* A.Spec m sp
    doStructured (A.Spec m sp s) = doStructured s >>* A.Spec m sp
    
