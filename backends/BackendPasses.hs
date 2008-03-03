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

-- | Passes associated with the backends
module BackendPasses where

import Control.Monad.State
import Data.Generics
import qualified Data.Set as Set

import qualified AST as A
import CompState
import Pass
import Types

-- | Identify processes that we'll need to compute the stack size of.
identifyParProcs :: Data t => t -> PassM t
identifyParProcs = doGeneric `extM` doProcess
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric identifyParProcs
  
    doProcess :: A.Process -> PassM A.Process
    doProcess p@(A.Par _ _ s) = findProcs s >> return p
    doProcess p = doGeneric p

    findProcs :: A.Structured A.Process -> PassM ()
    findProcs (A.Rep _ _ s) = findProcs s
    findProcs (A.Spec _ spec s) = doGeneric spec >> findProcs s
    findProcs (A.ProcThen _ p s) = doGeneric p >> findProcs s
    findProcs (A.Several _ ss) = sequence_ $ map findProcs ss
    findProcs (A.Only _ (A.ProcCall _ n _))
        = modify (\cs -> cs { csParProcs = Set.insert n (csParProcs cs) })

transformWaitFor :: Data t => t -> PassM t
transformWaitFor = doGeneric `extM` doAlt
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric transformWaitFor
  
    doAlt :: A.Process -> PassM A.Process
    doAlt a@(A.Alt m pri s)
      = do (s',(specs,code)) <- runStateT (applyToOnly doWaitFor s) ([],[])
           if (null specs && null code)
             then return a
             else return $ A.Seq m $ foldr addSpec (A.Several m (code ++ [A.Only m $ A.Alt m pri s'])) specs
    doAlt p = doGeneric p
    
    addSpec :: Data a => (A.Structured a -> A.Structured a) -> A.Structured a -> A.Structured a
    addSpec spec inner = spec inner

    doWaitFor :: A.Alternative -> StateT ([A.Structured A.Process -> A.Structured A.Process], [A.Structured A.Process]) PassM A.Alternative
    doWaitFor a@(A.AlternativeWait m A.WaitFor e p)
      = do (specs, init) <- get
           id <- lift $ makeNonce "waitFor"
           let n = (A.Name m A.VariableName id)
           let var = A.Variable m n
           put (specs ++ [A.Spec m (A.Specification m n (A.Declaration m A.Time Nothing))], 
                init ++ [A.Only m $ A.GetTime m var, A.Only m $ A.Assign m [var] $ A.ExpressionList m [A.Dyadic m A.Plus (A.ExprVariable m var) e]])
           return $ A.AlternativeWait m A.WaitUntil (A.ExprVariable m var) p
               
    doWaitFor a = return a

-- | Declares a _sizes array for every array, statically sized or dynamically sized.
-- For each record type it declares a _sizes array too.

-- TODO must make sure that each expression is already pulled out into a variable

declareSizesArray :: Data t => t -> PassM t
declareSizesArray = doGeneric `ext1M` doStructured
  where
    append_sizes :: A.Name -> A.Name
    append_sizes n = n {A.nameName = A.nameName n ++ "_sizes"}
  
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric declareSizesArray

    doStructured :: Data a => A.Structured a -> PassM (A.Structured a)
    doStructured str@(A.Spec m sp@(A.Specification m' n spec) s)
      = do t <- typeOfSpec spec
           case t of
             Just (A.Array ds _) -> if elem A.UnknownDimension ds
               then do let sizeSpec = A.Specification m' (append_sizes n) (A.Declaration m' (A.Array [A.Dimension $ length ds] A.Int) Nothing)
                       return (A.Spec m sp $ A.Spec m sizeSpec $ s) -- TODO fix this
               else do let n_sizes = append_sizes n
                           sizeType = A.Array [A.Dimension $ length ds] A.Int
                           sizeLit = A.Literal m' sizeType $ A.ArrayLiteral m' $
                             map (A.ArrayElemExpr . A.Literal m' A.Int . A.IntLiteral m' . show . \(A.Dimension d) -> d) ds
                           sizeSpecType = A.IsExpr m' A.ValAbbrev sizeType sizeLit
                           sizeSpec = A.Specification m' n_sizes sizeSpecType
                       defineName n_sizes $ A.NameDef {
                         A.ndMeta = m'
                        ,A.ndName = A.nameName n_sizes
                        ,A.ndOrigName = A.nameName n_sizes
                        ,A.ndNameType = A.VariableName
                        ,A.ndType = sizeSpecType
                        ,A.ndAbbrevMode = A.ValAbbrev
                        ,A.ndPlacement = A.Unplaced}
                       return (A.Spec m sp $ A.Spec m sizeSpec $ s)
                             
             _ -> return str
    doStructured s = doGeneric s

--TODO add a pass for adding _sizes parameters to PROC arguments

-- | Flattens all multi-dimensional arrays into one-dimensional arrays, transforming all indexes
-- as appropriate.
flattenArrays :: Data t => t -> PassM t
flattenArrays = return -- TODO
