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

import Data.Char

intrinsicFunctions :: [(String, ([A.Type], [(A.Type, String)]))]
intrinsicFunctions =
    [ -- Multiple length arithmetic functions
      -- Appendix L of the occam 2 manual (and section J.1)
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
      -- Appendix M of the occam 2 manual (and section J.3)
    ] ++ concatMap doubleD [
      ("IEEECOMPARE", ([A.Int], [(A.Real32, "X"), (A.Real32, "Y")]))
    ] ++ concatMap doubleNum [
        ("IEEE32OP", ([A.Bool, A.Real32], [(A.Real32, "X"), (A.Int, "Rm"), (A.Int, "Op"), (A.Real32, "Y")]))
      , ("IEEE32REM", ([A.Bool, A.Real32], [(A.Real32, "X"), (A.Real32, "Y")]))
      , ("REAL32EQ", ([A.Bool], [(A.Real32, "X"), (A.Real32, "Y")]))
      , ("REAL32GT", ([A.Bool], [(A.Real32, "X"), (A.Real32, "Y")]))
      , ("REAL32OP", ([A.Real32], [(A.Real32, "X"), (A.Int, "Op"), (A.Real32, "Y")]))
      , ("REAL32REM", ([A.Real32], [(A.Real32, "X"), (A.Real32, "Y")]))


      -- Floating point functions
      -- Appendix K of the occam 2 manual (and section J.2)
    ] ++ [
        ("ARGUMENT.REDUCE", ([A.Bool, A.Int32, A.Real32], [(A.Real32, "X"), (A.Real32, "Y"), (A.Real32, "Y.err")]))    
      , ("DARGUMENT.REDUCE", ([A.Bool, A.Int32, A.Real64], [(A.Real64, "X"), (A.Real64, "Y"), (A.Real64, "Y.err")]))
    ] ++ concatMap doubleD [
        simple "ABS"
      , ("COPYSIGN", ([A.Real32], [(A.Real32, "X"), (A.Real32, "Y")]))
      , simple "DIVBY2"
      , ("FLOATING.UNPACK", ([A.Int, A.Real32], [(A.Real32, "X")]))
      , simple "FPINT"
      , query "ISNAN"
      , simple "LOGB"
      , simple "MINUSX"
      , simple "MULBY2"
      , ("NEXTAFTER", ([A.Real32], [(A.Real32, "X"), (A.Real32, "Y")]))
      , query "NOTFINITE"
      , ("ORDERED", ([A.Bool], [(A.Real32, "X"), (A.Real32, "Y")]))
      , ("SCALEB", ([A.Real32], [(A.Real32, "X"), (A.Int, "n")]))
      , simple "SQRT"      
      ]

      -- Elementary floating point functions
      -- Appendix N of the occam 2 manual (and section J.4)
      ++ [(n, ts) | (n, (ts, _)) <- simpleFloatIntrinsics]
      ++ [("RAN", ([A.Real32, A.Int32], [(A.Int32, "N")]))]
    where
      query n = (n, ([A.Bool], [(A.Real32, "X")]))
      simple n = (n, ([A.Real32], [(A.Real32, "X")]))
      
      doubleNum orig@(n, (rs, ps)) = [orig, (map rep n, (map dt rs, zip (map (dt . fst) ps) (map snd ps)))]
        where
          rep '3' = '6'
          rep '2' = '4'
          rep c = c

      doubleD orig@(n, (rs, ps)) = [orig, ("D"++n, (map dt rs, zip (map (dt . fst) ps) (map snd ps)))]

      dt :: A.Type -> A.Type
      dt A.Real32 = A.Real64
      dt A.Int32 = A.Int64
      dt t = t

simpleFloatIntrinsics :: [(String, (([A.Type], [(A.Type, String)]), String))]
simpleFloatIntrinsics = concatMap double $
    -- Same order as occam manual:
  [("ALOG", ([A.Real32], [(A.Real32, "X")]), "log")
  ,("ALOG10", ([A.Real32], [(A.Real32, "X")]), "log10")
  ] ++ map s [
    "EXP",
    "TAN",
    "SIN",
    "ASIN",
    "COS",
    "ACOS",
    "SINH",
    "COSH",
    "TANH",
    "ATAN",
    "ATAN2"
  ]
  ++ [("POWER", ([A.Real32], [(A.Real32, "X"), (A.Real32, "Y")]), "pow")]
  where
    s n = (n, ([A.Real32], [(A.Real32, "X")]), map toLower n)
    
    double (occn, ts@(rts, pts), cn) = [(occn, (ts, cn++"f")),
      ("D"++occn, ((map dt rts, zip (map (dt . fst) pts) (map snd pts)), cn))]
    dt A.Real32 = A.Real64
    dt A.Int32 = A.Int64
    dt t = t

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
