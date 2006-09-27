-- C output passes

module PhaseOutput (phaseOutput) where

import Tree
import Pass
import BaseTransforms

bases = [baseTransformOc, baseTransformInt, baseTransformC]

phaseOutput
  = (Phase "C output"
      [
        ("Convert expressions", makePass () convExpressions bases)
      ])

convExpressions :: Transform ()
convExpressions next top node
  = case node of
    _ -> next node

