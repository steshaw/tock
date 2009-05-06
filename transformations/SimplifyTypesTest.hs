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

-- | Tests for 'SimplifyTypes'.
module SimplifyTypesTest (tests) where

import Control.Monad.State
import Data.Generics (Data)
import Test.HUnit hiding (State)

import CompState
import qualified AST as A
import Metadata
import Pass
import Pattern
import SimplifyTypes
import TagAST
import TestUtils
import Traversal
import TreeUtils

m :: Meta
m = emptyMeta

setupState :: State CompState ()
setupState
    =  do defineUserDataType "MYINT" A.Int

testResolveNamedTypes :: Test
testResolveNamedTypes = TestLabel "testResolveNamedTypes" $ TestList
  [ ok    0 A.Int
            A.Int
  , ok    1 myint
            A.Int
  , ok    2 (array10 myint)
            (array10 A.Int)
  ]
  where
    ok :: (PolyplateM a (OneOpM A.Type) BaseOpM
          ,PolyplateM a BaseOpM (OneOpM A.Type)
          ,Data a, Data b) => Int -> a -> b -> Test
    ok n inp exp = TestCase $ testPass ("testResolveNamedTypes" ++ show n)
                                       exp resolveNamedTypes inp setupState

    myint = A.UserDataType (simpleName "MYINT")
    array10 = A.Array [dimension 10]

tests :: Test
tests = TestLabel "SimplifyTypesTest" $ TestList
    [ testResolveNamedTypes
    ]
