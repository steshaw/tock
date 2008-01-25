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

module UsageCheck (checkPar, customVarCompare, Decl, labelFunctions, ParItems(..), Var(..), Vars(..)) where

import Data.Graph.Inductive
import qualified Data.Set as Set

import qualified AST as A
import Errors
import FlowGraph
import Metadata


newtype Var = Var A.Variable

data Vars = Vars {
  readVars :: Set.Set Var
  ,writtenVars :: Set.Set Var
  ,usedVars :: Set.Set Var -- for channels, barriers, etc
}

data Decl = ScopeIn String | ScopeOut String deriving (Show, Eq)

data ParItems a
  = ParItem a
  | ParItems [ParItems a]
  | RepParItem A.Replicator (ParItems a)

-- | Given a function to check a list of graph labels, a flow graph 
-- and a starting node, returns a list of monadic actions (slightly
-- more flexible than a monadic action giving a list) that will check
-- all PAR items in the flow graph
checkPar :: Monad m => ((Meta, ParItems a) -> m b) -> FlowGraph m a -> Node -> [m b]
checkPar = undefined -- TODO
--TODO is a start node actually necessary for checkPar?

labelFunctions :: Die m => GraphLabelFuncs m (Maybe Decl, Vars)
labelFunctions = undefined -- TODO
