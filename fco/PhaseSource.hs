-- Source-rewriting passes

module PhaseSource (phaseSource) where

import Tree
import Pass

phaseSource
  = (Phase "Source rewriting"
      [basePass1]
      [
        ("Nuke variable names", nukeVars)
      ])

basePass1 :: Pass
basePass1 next top node
  = case node of
      _ -> next node

nukeVars :: Pass
nukeVars next top node
  = case node of
      OcName n -> OcName "fish"
      _ -> next node

