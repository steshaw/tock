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

type Ptr a = IORef (Maybe (TypeExp a))

data TypeExp a
 = MutVar (Ptr a)
 | GenVar Int
 -- Either a list of integers that must fit, or a concrete type
 | NumLit (IORef (Either [Integer] A.Type))
 | OperType Constr [ TypeExp a ]
 deriving (Typeable)

-- Because Constr is not a member of Data, we must provide our own Data instance
-- here:

_typeExp_MutVarConstr, _typeExp_GenVarConstr, _typeExp_NumLitConstr,
  _typeExp_OperTypeConstr :: Constr
_typeExp_DataType :: DataType

_typeExp_MutVarConstr   = mkConstr _typeExp_DataType "MutVar"  [] Prefix
_typeExp_GenVarConstr   = mkConstr _typeExp_DataType "GenVar" [] Prefix
_typeExp_NumLitConstr   = mkConstr _typeExp_DataType "NumLit" [] Prefix
_typeExp_OperTypeConstr = mkConstr _typeExp_DataType "OperType" [] Prefix
_typeExp_DataType = mkDataType "TypeUnification.TypeExp"
  [ _typeExp_MutVarConstr
  , _typeExp_GenVarConstr
  , _typeExp_NumLitConstr
  , _typeExp_OperTypeConstr
  ]

instance Data a => Data (TypeExp a) where
  gfoldl f z (MutVar x)     = z MutVar `f` x
  gfoldl f z (GenVar x)     = z GenVar `f` x
  gfoldl f z (NumLit x)     = z NumLit `f` x
  -- We leave the Constr item untouched, as it is not of type Data:
  gfoldl f z (OperType x y) = z (OperType x) `f` y
  toConstr (MutVar {})      = _typeExp_MutVarConstr
  toConstr (GenVar {})      = _typeExp_GenVarConstr
  toConstr (NumLit {})      = _typeExp_NumLitConstr
  toConstr (OperType {})    = _typeExp_OperTypeConstr
  gunfold k z c = case constrIndex c of
                    1 -> (k) (z MutVar)
                    2 -> (k) (z GenVar)
                    3 -> (k) (z NumLit)
                    4 -> error "gunfold typeExp OperType"
                    _ -> error "gunfold typeExp"
  dataTypeOf _ = _typeExp_DataType
