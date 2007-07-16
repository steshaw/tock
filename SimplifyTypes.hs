-- | Simplify types in the AST.
module SimplifyTypes (simplifyTypes) where

import Control.Monad.State
import Data.Generics

import qualified AST as A
import Pass
import Types

simplifyTypes :: A.Process -> PassM A.Process
simplifyTypes = runPasses passes
  where
    passes =
      [ ("Resolve types in AST", resolveNamedTypes)
      , ("Resolve types in state", rntState)
      ]

-- | Turn named data types into their underlying types.
resolveNamedTypes :: Data t => t -> PassM t
resolveNamedTypes = doGeneric `extM` doType
  where
    doGeneric :: Data t => t -> PassM t
    doGeneric = makeGeneric resolveNamedTypes

    doType :: A.Type -> PassM A.Type
    doType t@(A.UserDataType _) = underlyingType t
    doType t = doGeneric t

-- | Resolve named types in CompState.
rntState :: A.Process -> PassM A.Process
rntState p
    =  do st <- get
          st' <- resolveNamedTypes st
          put st'
          return p

