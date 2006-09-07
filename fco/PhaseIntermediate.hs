-- Intermediate passes

module PhaseIntermediate (phaseIntermediate) where

import Tree
import Pass
import BasePasses

phaseIntermediate
  = (Phase "Intermediate mangling"
      [basePassOc, basePassInt]
      [
        ("Gather declarations", gatherDecls)
      ])

gatherDecls :: Pass
gatherDecls next top node
  = case node of
      OcDecl d c -> let c' = top c
                        d' = top d
                    in
                    case c' of
                      IntDeclSet ds cs -> IntDeclSet (d':ds) cs
                      _ -> IntDeclSet [d'] c'
      _ -> next node

