-- C output passes

module PhaseOutput (phaseOutput) where

import Tree
import Pass
import BasePasses

phaseOutput
  = (Phase "C output"
      [basePassOc, basePassInt, basePassC]
      [
        ("Convert expressions", convExpressions)
      ])

convExpressions :: Pass
convExpressions next top node
  = case node of
    _ -> next node

