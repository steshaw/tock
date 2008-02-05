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

-- | Identify processes that we'll need to compute the stack size of.
identifyParProcs :: Pass
identifyParProcs = everywhereM (mkM doProcess)
  where
    doProcess :: A.Process -> PassM A.Process
    doProcess p@(A.Par _ _ s) = findProcs s >> return p
    doProcess p = return p

    findProcs :: A.Structured A.Process -> PassM ()
    findProcs (A.Rep _ _ s) = findProcs s
    findProcs (A.Spec _ _ s) = findProcs s
    findProcs (A.ProcThen _ _ s) = findProcs s
    findProcs (A.Several _ ss) = sequence_ $ map findProcs ss
    findProcs (A.Only _ (A.ProcCall _ n _))
        = modify (\cs -> cs { csParProcs = Set.insert n (csParProcs cs) })

transformWaitFor :: Data t => t -> PassM t
transformWaitFor = everywhereM (mkM doAlt)
  where
    doAlt :: A.Process -> PassM A.Process
    doAlt a@(A.Alt m pri s)
      = do (a',(specs,code)) <- runStateT (everywhereM (mkM doWaitFor) a) ([],[])
           if (null specs && null code)
             then return a
             else return $ A.Seq m $ foldr addSpec (A.Several m (code ++ [A.Only m a'])) specs
    doAlt p = return p
    
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
