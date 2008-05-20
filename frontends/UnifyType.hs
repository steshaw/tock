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

module UnifyType where

import Data.Generics
import Data.IORef

import qualified AST as A
import Metadata

type Ptr a = IORef (Maybe (TypeExp a))

data Typeable a => TypeExp a
 = MutVar Meta (Ptr a)
 | GenVar Meta Int
 -- Either a list of integers that must fit, or a concrete type
 | NumLit Meta (IORef (Either [(Meta, Integer)] A.Type))
 | OperType Meta String ([A.Type] -> A.Type) [ TypeExp a ]
 deriving (Typeable, Data)
