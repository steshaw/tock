{-
Tock: a compiler for parallel languages
Copyright (C) 2008  University of Kent

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

-- | Simplify abbreviations.
module SimplifyAbbrevs (
    simplifyAbbrevs
  , removeInitial
  , removeResult
  , abbrevCheckPass
  ) where

import Control.Monad.State
import Data.Generics (Data)
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified AST as A
import CompState
import Errors
import Metadata
import OrdAST()
import Pass
import qualified Properties as Prop
import ShowCode
import Traversal
import UsageCheckUtils
import Utils

simplifyAbbrevs :: [Pass A.AST]
simplifyAbbrevs =
    [ removeInitial
    , removeResult
    , updateAbbrevsInState
    ]

-- | Rewrite 'InitialAbbrev' into a variable and an assignment.
removeInitial :: PassOnOps (ExtOpMS BaseOpM)
removeInitial
    = pass "Remove INITIAL abbreviations"
           []
           [Prop.initialRemoved]
           (applyBottomUpMS doStructured)
  where
    doStructured :: TransformStructured (ExtOpMS BaseOpM)
    doStructured (A.Spec m spec s) = doSpec m spec s
    doStructured s = return s

    -- FIXME: When we add mobile support, we'll need to make a decision between
    -- ValAbbrev and Abbrev based on whether the type in question is mobile.

    doSpec :: forall t. Data t =>
              Meta -> A.Specification
              -> A.Structured t -> PassM (A.Structured t)
    doSpec m spec@(A.Specification m' n st) inner
        = case st of
            -- INITIAL abbreviation
            --
            --   INITIAL INT foo IS bar:
            --   inner
            -- ->
            --   INT foo:
            --   PROCTHEN
            --     foo := bar
            --     inner
            A.Is m'' A.InitialAbbrev t (A.ActualExpression e) ->
              return $ declareAssign n t e inner

            -- INITIAL retyping
            --
            --   INITIAL INT foo RETYPES bar:
            --   inner
            -- ->
            --   VAL INT temp RETYPES bar:
            --   INT foo:
            --   PROCTHEN
            --     foo := temp
            --     inner
            A.RetypesExpr m'' A.InitialAbbrev t e ->
               do temp <- defineNonce m' "initial_retypes_expr" st A.ValAbbrev
                  let e = A.ExprVariable m' (specVar temp)
                  return $ A.Spec m temp $
                             declareAssign n t e inner

            -- PROC -- look for INITIAL formals
            --
            --   PROC foo (INITIAL INT bar)
            --     process
            --   :
            --   inner
            -- ->
            --   PROC foo (VAL INT temp)
            --     SEQ
            --       INT bar:
            --       PROCTHEN
            --         bar := temp
            --         process
            --   :
            --   inner
            A.Proc m'' sm fs (Just p) ->
               do -- Find the INITIAL formals, and note their positions.
                  let (positions, fromFS)
                        = unzip [(i, f)
                                 | (i, f@(A.Formal A.InitialAbbrev _ _))
                                     <- zip [0 ..] fs]

                  -- Define names for new formals.
                  temps <- sequence [defineNonce m'
                                                 "initial_formal"
                                                 (A.Declaration m' t)
                                                 A.ValAbbrev
                                     | A.Formal _ t _ <- fromFS]

                  -- Replace the old formals with new ValAbbrevs.
                  let fs' = foldl (\fs (A.Specification _ n _,
                                        A.Formal _ t _,
                                        pos) ->
                                    replaceAt pos
                                              (A.Formal A.ValAbbrev t n)
                                              fs
                                  )
                                  fs (zip3 temps fromFS positions)

                  -- Wrap the inner process to declare the old names as
                  -- variables and copy the right values into them.
                  -- (We reverse the list so the first formal is outermost.)
                  let p' = foldl (\p (temp, A.Formal _ t n) ->
                                    let e = A.ExprVariable m' (specVar temp) in
                                    A.Seq m' (declareAssign n t e $
                                                A.Only m' p))
                                 p (reverse $ zip temps fromFS)

                  let spec' = A.Specification m' n (A.Proc m'' sm fs' (Just p'))
                  return $ A.Spec m spec' inner

            _ -> leave
      where
        leave :: PassM (A.Structured t)
        leave = return $ A.Spec m spec inner

        declareAssign :: Data s =>
                      A.Name -> A.Type -> A.Expression
                      -> A.Structured s -> A.Structured s
        declareAssign n t e s
            = A.Spec m (A.Specification m' n $ A.Declaration m' t) $
                A.ProcThen m' (A.Assign m'
                                        [A.Variable m' n]
                                        (A.ExpressionList m' [e])) $
                  s

        specVar :: A.Specification -> A.Variable
        specVar (A.Specification m n _) = A.Variable m n

-- | Rewrite 'ResultAbbrev' into just 'Abbrev'.
removeResult :: Alloy t (OneOp A.AbbrevMode) BaseOp => Pass t
removeResult
    = pass "Remove RESULT abbreviations"
           []
           [Prop.resultRemoved]
           (return . applyBottomUp doAbbrevMode)
  where
    doAbbrevMode :: A.AbbrevMode -> A.AbbrevMode
    doAbbrevMode A.ResultAbbrev = A.Abbrev
    doAbbrevMode s = s

-- | Rewrite abbreviation modes in the state.
updateAbbrevsInState :: Pass t
updateAbbrevsInState
    = pass "Update INITIAL and RESULT abbreviations in state"
           [Prop.initialRemoved, Prop.resultRemoved]
           []
           (\v -> modify (applyBottomUp doAbbrevMode) >> return v)
  where
    doAbbrevMode :: A.AbbrevMode -> A.AbbrevMode
    doAbbrevMode A.InitialAbbrev = A.Original
    doAbbrevMode A.ResultAbbrev = A.Abbrev
    doAbbrevMode s = s

type AbbrevCheckM = StateT [Map.Map Var Bool] PassM

type AbbrevCheckOps
  = A.Variable
    :-* A.Process
    :-* A.InputItem
    :-* ExtOpMS BaseOpM

abbrevCheckPass :: (AlloyA t AbbrevCheckOps BaseOpM, AlloyA t BaseOpM AbbrevCheckOps) => Pass t
abbrevCheckPass
    = pass "Abbreviation checking" [] []
           ({-passOnlyOnAST "abbrevCheck" $ -} flip evalStateT [Map.empty] . recurse)
  where
    ops :: AbbrevCheckOps AbbrevCheckM
    ops = doVariable :-* doProcess :-* doInputItem :-* opMS (ops, doStructured)

    descend :: DescendM AbbrevCheckM AbbrevCheckOps
    descend = makeDescendM ops
    recurse :: RecurseM AbbrevCheckM AbbrevCheckOps
    recurse = makeRecurseM ops

    pushRecurse :: (AlloyA a AbbrevCheckOps BaseOpM) => a -> AbbrevCheckM a
    pushRecurse x = modify (Map.empty:) >> recurse x
    pop :: StateT [Map.Map Var Bool] PassM ()
    pop = modify $ \st -> case st of
      (m:m':ms) -> Map.unionWith (||) m m' : ms
      _ -> st

    record b v = modify (\(m:ms) -> (Map.insertWith (||) (Var v) b m : ms))

    nameIsNonce :: A.Name -> StateT [Map.Map Var Bool] PassM Bool
    nameIsNonce n
      = do names <- lift getCompState >>* csNames
           case fmap A.ndNameSource $ Map.lookup (A.nameName n) names of
             Just A.NameNonce -> return True
             _ -> return False

    -- Judging by the cgtests (cgtest18, line 232), we should turn off usage checking
    -- on an abbreviation if either the RHS *or* the LHS is exempt by a PERMITALIASEs
    -- pragma

    doStructured :: (AlloyA (A.Structured t) BaseOpM AbbrevCheckOps
                    ,AlloyA (A.Structured t) AbbrevCheckOps BaseOpM, Data t) =>
      A.Structured t -> AbbrevCheckM (A.Structured t)
    doStructured s@(A.Spec _ (A.Specification _ n (A.Is _ A.Abbrev _ (A.ActualVariable v))) scope)
      = do nonce <- nameIsNonce n
           ex <- isNameExempt n
           if nonce || ex
             then descend s >> return ()
             else do pushRecurse scope
                     checkAbbreved v "Abbreviated variable % used inside the scope of the abbreviation"
                     pop
           return s
    doStructured s@(A.Spec _ (A.Specification m n (A.Is _ A.ValAbbrev _ (A.ActualVariable v))) scope)
      = do nonce <- nameIsNonce n
           ex <- isNameExempt n
           if nonce || ex
             then descend s >> return ()
             else do pushRecurse scope
                     checkAbbreved v "Abbreviated variable % used inside the scope of the abbreviation"
                     checkNotWritten (A.Variable m n) "VAL-abbreviated variable % written-to inside the scope of the abbreviation"
                     pop
           return s
    doStructured s@(A.Spec _ (A.Specification m n (A.Is _ A.ValAbbrev _ (A.ActualExpression e))) scope)
      = do nonce <- nameIsNonce n
           ex <- isNameExempt n
           if nonce || ex
             then descend s >> return ()
             else do pushRecurse scope
                     checkNotWritten (A.Variable m n) "VAL-abbreviated variable % written-to inside the scope of the abbreviation"
                     sequence_ [checkNotWritten v
                       "Abbreviated variable % used inside the scope of the abbreviation"
                       | A.ExprVariable _ v <- listifyDepth (const True) e]
                     pop
           return s
    doStructured s = descend s

    isExempt :: A.Variable -> StateT [Map.Map Var Bool] PassM Bool
    isExempt (A.DirectedVariable _ _ v) = isExempt v
    isExempt (A.DerefVariable _ v) = isExempt v
    isExempt (A.SubscriptedVariable _ _ v) = isExempt v
    isExempt (A.VariableSizes {}) = return False -- They are read-only anyway
    isExempt (A.Variable _ n) = isNameExempt n

    isNameExempt :: A.Name -> StateT [Map.Map Var Bool] PassM Bool
    isNameExempt n
      = do st <- lift getCompState
           case Map.lookup (A.nameName n) (csNameAttr st) of
             Just attrs | NameAliasesPermitted `Set.member` attrs -> return True
             _ -> return False

    --In the map, True means written-to (and maybe read), False means just read
    
    checkAbbreved :: A.Variable -> String -> StateT [Map.Map Var Bool] PassM ()
    checkAbbreved v@(A.Variable {}) msg = checkNone v msg
    checkAbbreved v@(A.DirectedVariable {}) msg = checkNone v msg
    checkAbbreved (A.SubscriptedVariable _ sub v) msg
      = sequence_ [checkNotWritten subV msg | subV <- listifyDepth (const True) sub]

    checkNone :: A.Variable -> String -> StateT [Map.Map Var Bool] PassM ()
    checkNone v msg
      = do m <- get >>* head
           ex <- isExempt v
           when (not ex) $
             case Map.lookup (Var v) m of
               Nothing -> return ()
               _ -> lift $ diePC (findMeta v) $ formatCode msg v

    checkNotWritten :: A.Variable -> String -> StateT [Map.Map Var Bool] PassM ()
    checkNotWritten v msg
      = do m <- get >>* head
           ex <- isExempt v
           when (not ex) $
             case Map.lookup (Var v) m of
               Just True -> lift $ diePC (findMeta v) $ formatCode msg v
               _ -> return ()
           

    doVariable :: A.Variable -> StateT [Map.Map Var Bool] PassM A.Variable
    doVariable v = record False v >> descend v

    doProcess :: A.Process -> StateT [Map.Map Var Bool] PassM A.Process
    doProcess p@(A.Assign m lhs rhs)
          = do mapM (record True) lhs
               mapM descend lhs -- To catch sub-variables
               recurse rhs
               return p
    doProcess p = descend p

    doInputItem :: A.InputItem -> StateT [Map.Map Var Bool] PassM A.InputItem
    doInputItem i@(A.InCounted m a b)
          = do mapM (record True) [a, b]
               descend i -- To catch sub-variables
    doInputItem i@(A.InVariable m a)
          = do record True a
               descend i -- To catch sub-variables
