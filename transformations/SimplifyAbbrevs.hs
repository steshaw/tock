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
  ) where

import Data.Generics

import qualified AST as A
import CompState
import Control.Monad.State
import Metadata
import Pass
import qualified Properties as Prop
import Traversal
import Utils

simplifyAbbrevs :: [Pass]
simplifyAbbrevs =
    [ removeInitial
    , removeResult
    , updateAbbrevsInState
    ]

-- | Rewrite 'InitialAbbrev' into a variable and an assignment.
removeInitial :: Pass
removeInitial
    = pass "Remove INITIAL abbreviations"
           []
           [Prop.initialRemoved]
           (applyDepthSM doStructured)
  where
    doStructured :: Data t => A.Structured t -> PassM (A.Structured t)
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
            A.IsExpr m'' A.InitialAbbrev t e ->
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
            A.Proc m'' sm fs p ->
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

                  let spec' = A.Specification m' n (A.Proc m'' sm fs' p')
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
removeResult :: Pass
removeResult
    = pass "Remove RESULT abbreviations"
           []
           [Prop.resultRemoved]
           (applyDepthM (return . doAbbrevMode))
  where
    doAbbrevMode :: A.AbbrevMode -> A.AbbrevMode
    doAbbrevMode A.ResultAbbrev = A.Abbrev
    doAbbrevMode s = s

-- | Rewrite abbreviation modes in the state.
updateAbbrevsInState :: Pass
updateAbbrevsInState
    = pass "Update INITIAL and RESULT abbreviations in state"
           [Prop.initialRemoved, Prop.resultRemoved]
           []
           (\v -> get >>= applyDepthM (return . doAbbrevMode) >>= put >> return v)
  where
    doAbbrevMode :: A.AbbrevMode -> A.AbbrevMode
    doAbbrevMode A.InitialAbbrev = A.Original
    doAbbrevMode A.ResultAbbrev = A.Abbrev
    doAbbrevMode s = s
