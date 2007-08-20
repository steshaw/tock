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

module TestMain () where

import qualified RainParseTest (tests)
import qualified RainPassTest (tests)
import qualified UsageCheckTest (tests)
import qualified PassTest (tests)
import Test.HUnit

main :: IO ()
main = do runTestTT $ TestList
            [
              PassTest.tests
              ,RainParseTest.tests
              ,RainPassTest.tests
              ,UsageCheckTest.tests
            ]
          return ()
