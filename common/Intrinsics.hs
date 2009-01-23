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

-- | Definitions of intrinsic FUNCTIONs and PROCs.
module Intrinsics where

import qualified AST as A

intrinsicFunctions :: [(String, ([A.Type], [(A.Type, String)]))]
intrinsicFunctions =
    [ -- Multiple length arithmetic functions
      -- Appendix L of the occam 2 manual
      ("ASHIFTLEFT", ([A.Int], [(A.Int, "argument"), (A.Int, "places")]))
    , ("ASHIFTRIGHT", ([A.Int], [(A.Int, "argument"), (A.Int, "places")]))
    , ("LONGADD", ([A.Int], [(A.Int, "left"), (A.Int, "right"), (A.Int, "carry.in")]))
    , ("LONGDIFF", ([A.Int,A.Int], [(A.Int, "left"), (A.Int, "right"), (A.Int, "borrow.in")]))
    , ("LONGDIV", ([A.Int,A.Int], [(A.Int, "dividend.hi"), (A.Int, "dividend.lo"), (A.Int, "divisor")]))
    , ("LONGPROD", ([A.Int,A.Int], [(A.Int, "left"), (A.Int, "right"), (A.Int, "carry.in")]))
    , ("LONGSUB", ([A.Int], [(A.Int, "left"), (A.Int, "right"), (A.Int, "borrow.in")]))
    , ("LONGSUM", ([A.Int,A.Int], [(A.Int, "left"), (A.Int, "right"), (A.Int, "carry.in")]))
    , ("NORMALISE", ([A.Int, A.Int, A.Int], [(A.Int, "hi.in"), (A.Int, "lo.in")]))
    , ("ROTATELEFT", ([A.Int], [(A.Int, "argument"), (A.Int, "places")]))
    , ("ROTATERIGHT", ([A.Int], [(A.Int, "argument"), (A.Int, "places")]))
    , ("SHIFTLEFT", ([A.Int, A.Int], [(A.Int, "hi.in"), (A.Int, "lo.in"), (A.Int, "places")]))
    , ("SHIFTRIGHT", ([A.Int, A.Int], [(A.Int, "hi.in"), (A.Int, "lo.in"), (A.Int, "places")]))

      -- IEEE floating point arithmetic
      -- Appendix M of the occam 2 manual
    , ("REAL32OP", ([A.Real32], [(A.Real32, "X"), (A.Int, "Op"), (A.Real32, "Y")]))

    , ("SQRT", ([A.Real32], [(A.Real32, "value")]))
    , ("DSQRT", ([A.Real64], [(A.Real64, "value")]))
    ]

intrinsicProcs :: [(String, [(A.AbbrevMode, A.Type, String)])]
intrinsicProcs =
    [ ("ASSERT", [(A.ValAbbrev, A.Bool, "value")])
    , ("RESCHEDULE", [])
    ]

rainIntrinsicFunctions :: [(String, ([A.Type], [(A.Type, String)]))]
rainIntrinsicFunctions =
    -- Time functions:
    [ ("toSeconds", ([A.Real64], [(A.Time, "time")]))
    , ("toMillis", ([A.Int64], [(A.Time, "time")]))
    , ("toMicros", ([A.Int64], [(A.Time, "time")]))
    , ("toNanos", ([A.Int64], [(A.Time, "time")]))
    , ("fromSeconds", ([A.Time], [(A.Real64, "value")]))
    , ("fromMillis", ([A.Time], [(A.Int64, "value")]))
    , ("fromMicros", ([A.Time], [(A.Int64, "value")]))
    , ("fromNanos", ([A.Time], [(A.Int64, "value")]))
    ]
