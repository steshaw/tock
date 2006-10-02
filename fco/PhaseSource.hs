-- Source-rewriting passes

module PhaseSource (phaseSource) where

import Tree
import Pass
import BaseTransforms
import Control.Monad.State

bases = [baseTransformOc]

phaseSource
  = (Phase "Source rewriting"
      [
        ("Simplify", makePass () simplify bases),
        ("C-ify identifiers", makePass () cifyIdentifiers bases)
      ])

simplify :: Transform ()
simplify next top node
  = case node of
      -- FIXME rewrite stuff like OcFuncIs -> OcFunc
      -- FIXME could we even rewrite procs and functions to the same thing?
      _ -> next node

cifyIdentifiers :: Transform ()
cifyIdentifiers next top node
  = case node of
      OcName n -> return $ OcName [if c == '.' then '_' else c | c <- n]
      _ -> next node

