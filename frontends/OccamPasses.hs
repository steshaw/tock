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

-- | The occam-specific frontend passes.
module OccamPasses (occamPasses, foldConstants, checkConstants,
                    checkRetypes) where

import Control.Monad.State
import Data.Generics
import System.IO

import qualified AST as A
import CompState
import Errors
import EvalConstants
import EvalLiterals
import Metadata
import Pass
import qualified Properties as Prop
import ShowCode
import Types

-- | Occam-specific frontend passes.
occamPasses :: [Pass]
occamPasses = makePassesDep' ((== FrontendOccam) . csFrontend)
    [ ("Fold constants", foldConstants,
       [],
       [Prop.constantsFolded])
    , ("Check mandatory constants", checkConstants,
       [Prop.constantsFolded],
       [Prop.constantsChecked])
    , ("Check retyping", checkRetypes,
       [],
       [Prop.retypesChecked])
    , ("Dummy occam pass", dummyOccamPass,
       [],
       Prop.agg_namesDone ++ [Prop.expressionTypesChecked,
                              Prop.inferredTypesRecorded, Prop.mainTagged,
                              Prop.processTypesChecked])
    ]

-- | Fold constant expressions.
foldConstants :: Data t => t -> PassM t
foldConstants = doGeneric `extM` doSpecification `extM` doExpression
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric foldConstants

    -- When an expression is abbreviated, try to fold it, and update its
    -- definition so that it can be used when folding later expressions.
    doSpecification :: A.Specification -> PassM A.Specification
    doSpecification s@(A.Specification m n (A.IsExpr m' am t e))
        =  do e' <- doExpression e
              let st' = A.IsExpr m' am t e'
              modifyName n (\nd -> nd { A.ndType = st' })
              return $ A.Specification m n st'
    doSpecification s = doGeneric s

    -- For all other expressions, just try to fold them.
    -- We recurse into the expression first so that we fold subexpressions of
    -- non-constant expressions too.
    doExpression :: A.Expression -> PassM A.Expression
    doExpression e
        =  do e' <- doGeneric e
              (e'', _, _) <- constantFold e'
              return e''

-- | Check that things that must be constant are.
checkConstants :: Data t => t -> PassM t
checkConstants = doGeneric `extM` doDimension `extM` doOption
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric checkConstants

    -- Check array dimensions are constant.
    doDimension :: A.Dimension -> PassM A.Dimension
    doDimension d@(A.Dimension e)
        =  do when (not $ isConstant e) $
                diePC (findMeta e) $ formatCode "Array dimension must be constant: %" e
              doGeneric d
    doDimension d = doGeneric d

    -- Check case options are constant.
    doOption :: A.Option -> PassM A.Option
    doOption o@(A.Option _ es _)
        =  do sequence_ [when (not $ isConstant e) $
                           diePC (findMeta e) $ formatCode "Case option must be constant: %" e
                         | e <- es]
              doGeneric o
    doOption o = doGeneric o

-- | Check that retyping is safe.
checkRetypes :: Data t => t -> PassM t
checkRetypes = everywhereASTM doSpecType
  where
    doSpecType :: A.SpecType -> PassM A.SpecType
    doSpecType st@(A.Retypes m _ t v)
        =  do fromT <- typeOfVariable v
              checkRetypes m fromT t
              return st
    doSpecType st@(A.RetypesExpr m _ t e)
        =  do fromT <- typeOfExpression e
              checkRetypes m fromT t
              return st
    doSpecType st = return st

    checkRetypes :: Meta -> A.Type -> A.Type -> PassM ()
    checkRetypes m fromT toT
        =  do (fromBI, fromN) <- evalBytesInType fromT
              (toBI, toN) <- evalBytesInType toT
              case (fromBI, toBI, fromN, toN) of
                (_, BIManyFree, _, _) ->
                  dieP m "Multiple free dimensions in retype destination type"
                (BIJust _, BIJust _, Just a, Just b) ->
                  when (a /= b) $
                    dieP m "Sizes do not match in retype"
                (BIJust _, BIOneFree _ _, Just a, Just b) ->
                  when (not ((b <= a) && (a `mod` b == 0))) $
                    dieP m "Sizes do not match in retype"
                (BIOneFree _ _, BIJust _, Just a, Just b) ->
                  when (not ((a <= b) && (b `mod` a == 0))) $
                    dieP m "Sizes do not match in retype"
                -- Otherwise we must do a runtime check.
                _ -> return ()

    evalBytesInType :: A.Type -> PassM (BytesInResult, Maybe Int)
    evalBytesInType t
        =  do bi <- bytesInType t
              n <- case bi of
                     BIJust e -> maybeEvalIntExpression e
                     BIOneFree e _ -> maybeEvalIntExpression e
                     _ -> return Nothing
              return (bi, n)

-- | A dummy pass for things that haven't been separated out into passes yet.
dummyOccamPass :: Data t => t -> PassM t
dummyOccamPass = return

