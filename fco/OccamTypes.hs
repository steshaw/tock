-- Data types for occam abstract syntax
-- This is intended to be imported qualified:
--   import qualified OccamTypes as O

module OccamTypes where

import Data.Generics

type Name = String
data Tag = Tag Name
  deriving (Show, Eq, Typeable, Data)

data Type =
  Bool
  | Byte
  | Int | Int16 | Int32 | Int64
  | Real32 | Real64
  | Array Expression Type
  | UnsizedArray Type
  | UserType Name
  | Chan Type
  | Counted Type Type
  | Any
  | Timer
  | Port Type
  deriving (Show, Eq, Typeable, Data)

data ConversionMode =
  DefaultConversion
  | Round
  | Trunc
  deriving (Show, Eq, Typeable, Data)

data Slice =
  SliceFromFor Expression Expression
  | SliceFrom Expression
  | SliceFor Expression
  deriving (Show, Eq, Typeable, Data)

data LiteralRepr =
  RealLiteral String
  | IntLiteral String
  | ByteLiteral String
  | StringLiteral String
  | ArrayLiteral [Expression]
  | SlicedLiteral Slice LiteralRepr
  deriving (Show, Eq, Typeable, Data)

data Variable =
  Variable Name
  | SlicedVariable Slice Variable
  | Subscript Expression Variable
  deriving (Show, Eq, Typeable, Data)

data Expression =
  Monadic MonadicOp Expression
  | Dyadic DyadicOp Expression Expression
  | MostPos Type
  | MostNeg Type
  | Size Type
  | Conversion ConversionMode Expression
  | ExprVariable Variable
  | Literal Type LiteralRepr
  | True
  | False
  | Table
  | FunctionCall Name [Expression]
  | BytesInType Type
  | OffsetOf Type Name
  deriving (Show, Eq, Typeable, Data)

data ExpressionList =
  FunctionCallList Name [Expression]
  | ExpressionList [Expression]
  deriving (Show, Eq, Typeable, Data)

data MonadicOp =
  MonadicBytesIn
  | MonadicSubtr
  | MonadicBitNot
  | MonadicNot
  | MonadicSize
  deriving (Show, Eq, Typeable, Data)

data DyadicOp =
  Add | Subtr | Mul | Div | Rem
  | Plus | Minus | Times
  | BitAnd | BitOr | BitXor
  | And | Or
  | Eq | NotEq | Less | More | LessEq | MoreEq
  | After
  deriving (Show, Eq, Typeable, Data)

data InputItem =
  InCounted Variable Variable
  | InVariable Variable
  deriving (Show, Eq, Typeable, Data)

data OutputItem =
  OutCounted Expression Expression
  | OutExpression Expression
  deriving (Show, Eq, Typeable, Data)

data Replicator = For Name Expression Expression
  deriving (Show, Eq, Typeable, Data)

data Choice = Choice Expression Process
  deriving (Show, Eq, Typeable, Data)

data Alternative =
  AltInput Input Process
  | GuardedAltInput Expression Input Process
  | GuardedSkip Expression Process
  deriving (Show, Eq, Typeable, Data)

data Option =
  Option [Expression] Process
  | Else Process
  deriving (Show, Eq, Typeable, Data)

data Variant = Variant Tag [InputItem] Process
  deriving (Show, Eq, Typeable, Data)

-- This represents something that can contain local replicators and specifications.
type Structured t = [StructEntry t]
data StructEntry t =
  Rep Replicator (Structured t)
  | Spec Specification (Structured t)
  | Only t
  deriving (Show, Eq, Typeable, Data)

data Input =
  InputSimple Variable [InputItem]
  | InputCase Variable (Structured Variant)
  | InputAfter Variable Expression
  deriving (Show, Eq, Typeable, Data)

data Specification =
  Place Name Expression
  | Declaration Type Name
  | Is Type Name Variable
  | ValIs Type Name Expression
  | DataTypeIs Name Type
  | DataTypeRecord Name Bool [(Type, Name)]
  | ProtocolIs Name [Type]
  | ProtocolCase Name [(Tag, [Type])]
  | Proc Name [(Type, Name)] Process
  | Function Name [Type] [(Type, Name)] ValueProcess
  | Retypes Name Variable
  | Reshapes Name Variable
  | ValRetypes Name Variable
  | ValReshapes Name Variable
  deriving (Show, Eq, Typeable, Data)

type ValueProcess = Structured ValOf
data ValOf = ValOf Process ExpressionList
  deriving (Show, Eq, Typeable, Data)

type Process = Structured ProcessEntry
data ProcessEntry =
  Assignment [Variable] ExpressionList
  | Input Input
  | Output Variable [OutputItem]
  | OutputCase Variable Tag [OutputItem]
  | Skip
  | Stop
  | Main
  | Seq [Process]
  | ReplicatedSeq Replicator Process
  | If (Structured Choice)
  | Case Expression (Structured Option)
  | While Expression Process
  | Par Bool (Structured Process)
  | PlacedPar (Structured Process)
  | Processor Expression Process
  | Alt Bool (Structured Alternative)
  | ProcCall Name [Expression]
  deriving (Show, Eq, Typeable, Data)

