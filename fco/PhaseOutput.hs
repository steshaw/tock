-- C output passes

module PhaseOutput (phaseOutput) where

import Tree
import Pass
import PhaseSource

phaseOutput
  = (Phase "C output"
      [basePass1, basePass9]
      [
        ("Convert expressions", convExpressions)
      ])

-- {{{ BEGIN basePass9
basePass9 :: Pass
basePass9 next top node
  = case node of
      CCode a -> CCode a
      _ -> next node
-- }}} END

convExpressions :: Pass
convExpressions next top node
  = case node of
    _ -> next node

