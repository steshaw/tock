-- Intermediate passes

module PhaseIntermediate (phaseIntermediate) where

import Tree
import Pass
import BaseTransforms

bases = [baseTransformOc, baseTransformInt]

phaseIntermediate
  = (Phase "Intermediate mangling"
      [
        ("Gather declarations", makePass () gatherDecls bases)
      ])

gatherDecls :: Transform ()
gatherDecls next top node
  = case node of
      OcDecl d c -> do
        c' <- top c
        d' <- top d
        return $ case c' of
          IntDeclSet ds cs -> IntDeclSet (d':ds) cs
          _ -> IntDeclSet [d'] c'
      _ -> next node

