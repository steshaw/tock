-- Source-rewriting passes

module PhaseSource (phaseSource) where

import qualified Tree as N
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
      -- FIXME rewrite stuff like N.FuncIs -> N.Func
      -- FIXME could we even rewrite procs and functions to the same thing?
      _ -> next node

cifyIdentifiers :: Transform ()
cifyIdentifiers next top node
  = case node of
      N.Name n -> return $ N.Name [if c == '.' then '_' else c | c <- n]
      _ -> next node

