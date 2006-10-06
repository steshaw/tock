-- Data types for occam abstract syntax
-- This is intended to be imported qualified:
--   import qualified AST as O

module AST where

import Data.Generics

data Name = Name String
  deriving (Show, Eq, Typeable, Data)

data Tag = Tag String
  deriving (Show, Eq, Typeable, Data)

data Type =
  Bool
  | Byte
  | Int | Int16 | Int32 | Int64
  | Real32 | Real64
  | Array Expression Type
  | ArrayUnsized Type
  | UserType Name
  | Chan Type
  | Counted Type Type
  | Any
  | Timer
  | Port Type
  | Val Type
  | Infer    -- for where the type is not given but can be worked out (e.g. "x IS y:")
  deriving (Show, Eq, Typeable, Data)

data ConversionMode =
  DefaultConversion
  | Round
  | Trunc
  deriving (Show, Eq, Typeable, Data)

data Subscript =
  Subscript Expression
  | SubscriptTag Tag
  | SubFromFor Expression Expression
  | SubFrom Expression
  | SubFor Expression
  deriving (Show, Eq, Typeable, Data)

data LiteralRepr =
  RealLiteral String
  | IntLiteral String
  | HexLiteral String
  | ByteLiteral String
  | StringLiteral String
  | ArrayLiteral [Expression]
  deriving (Show, Eq, Typeable, Data)

data Literal =
  Literal Type LiteralRepr
  | SubscriptedLiteral Subscript Literal
  deriving (Show, Eq, Typeable, Data)

data Variable =
  Variable Name
  | SubscriptedVariable Subscript Variable
  deriving (Show, Eq, Typeable, Data)

data Expression =
  Monadic MonadicOp Expression
  | Dyadic DyadicOp Expression Expression
  | MostPos Type
  | MostNeg Type
  | Size Type
  | Conversion ConversionMode Type Expression
  | ExprVariable Variable
  | ExprLiteral Literal
  | True
  | False
  | FunctionCall Name [Expression]
  | BytesInType Type
  | OffsetOf Type Tag
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
  Alternative Variable InputMode Process
  | AlternativeCond Expression Variable InputMode Process
  | AlternativeSkip Expression Process
  deriving (Show, Eq, Typeable, Data)

data Option =
  Option [Expression] Process
  | Else Process
  deriving (Show, Eq, Typeable, Data)

data Variant = Variant Tag [InputItem] Process
  deriving (Show, Eq, Typeable, Data)

-- This represents something that can contain local replicators and specifications.
data Structured t =
  Rep Replicator (Structured t)
  | Spec Specification (Structured t)
  | Only t
  | Several [Structured t]
  deriving (Show, Eq, Typeable, Data)

data InputMode =
  InputSimple [InputItem]
  | InputCase (Structured Variant)
  | InputAfter Expression
  deriving (Show, Eq, Typeable, Data)

type Specification = (Name, SpecType)
data SpecType =
  Place Expression
  | Declaration Type
  | Is Type Variable
  | ValIs Type Expression
  | DataTypeIs Type
  | DataTypeRecord Bool [(Type, Tag)]
  | ProtocolIs [Type]
  | ProtocolCase [(Tag, [Type])]
  | Proc [(Type, Name)] Process
  | Function [Type] [(Type, Name)] ValueProcess
  | Retypes Type Variable
  | Reshapes Type Variable
  | ValRetypes Type Variable
  | ValReshapes Type Variable
  deriving (Show, Eq, Typeable, Data)

data ValueProcess =
  ValOfSpec Specification ValueProcess
  | ValOf Process ExpressionList
  deriving (Show, Eq, Typeable, Data)

data Process =
  ProcSpec Specification Process
  | Assign [Variable] ExpressionList
  | Input Variable InputMode
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
  | Par Bool [Process]
  | ParRep Bool Replicator Process
  | PlacedPar (Structured Process)
  | Processor Expression Process
  | Alt Bool (Structured Alternative)
  | ProcCall Name [Expression]
  deriving (Show, Eq, Typeable, Data)

