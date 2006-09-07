-- Source-rewriting passes

module PhaseSource (phaseSource) where

import Tree
import Pass
import BasePasses

phaseSource
  = (Phase "Source rewriting"
      [basePassOc]
      [
        ("C-ify identifiers", cifyIdentifiers)
      ])

cifyIdentifiers :: Pass
cifyIdentifiers next top node
  = case node of
      OcName n -> OcName [if c == '.' then '_' else c | c <- n]
      _ -> next node

