-- | Definitions of intrinsic FUNCTIONs and PROCs.
module Intrinsics where

import qualified AST as A

intrinsicFunctions :: [(String, ([A.Type], [(A.Type, String)]))]
intrinsicFunctions =
    [ ("SQRT", ([A.Real32], [(A.Real32, "value")]))
    , ("DSQRT", ([A.Real64], [(A.Real64, "value")]))
    ]

intrinsicProcs :: [(String, [(A.AbbrevMode, A.Type, String)])]
intrinsicProcs =
    [ ("ASSERT", [(A.ValAbbrev, A.Bool, "value")])
    ]

