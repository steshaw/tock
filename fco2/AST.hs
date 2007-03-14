-- Data types for occam abstract syntax
-- This is intended to be imported qualified:
--   import qualified AST as A

module AST where

import Data.Generics
import Metadata

data Name = Name Meta String
  deriving (Show, Eq, Typeable, Data)

data Tag = Tag Meta String
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
  | Infer   -- for where the type is not given but can be worked out (e.g. "x IS y:")
  deriving (Show, Eq, Typeable, Data)

data ConversionMode =
  DefaultConversion
  | Round
  | Trunc
  deriving (Show, Eq, Typeable, Data)

data Subscript =
  Subscript Meta Expression
  | SubscriptTag Meta Tag
  | SubscriptFromFor Meta Expression Expression
  | SubscriptFrom Meta Expression
  | SubscriptFor Meta Expression
  deriving (Show, Eq, Typeable, Data)

data LiteralRepr =
  RealLiteral Meta String
  | IntLiteral Meta String
  | HexLiteral Meta String
  | ByteLiteral Meta String
  | StringLiteral Meta String
  | ArrayLiteral Meta [Expression]
  deriving (Show, Eq, Typeable, Data)

data Literal =
  Literal Meta Type LiteralRepr
  | SubscriptedLiteral Meta Subscript Literal
  deriving (Show, Eq, Typeable, Data)

data Channel =
  Channel Meta Name
  | SubscriptedChannel Meta Subscript Channel
  deriving (Show, Eq, Typeable, Data)

data Variable =
  Variable Meta Name
  | SubscriptedVariable Meta Subscript Variable
  deriving (Show, Eq, Typeable, Data)

data Expression =
  Monadic Meta MonadicOp Expression
  | Dyadic Meta DyadicOp Expression Expression
  | MostPos Meta Type
  | MostNeg Meta Type
  | Size Meta Type
  | Conversion Meta ConversionMode Type Expression
  | ExprVariable Meta Variable
  | ExprLiteral Meta Literal
  | True Meta
  | False Meta
  | FunctionCall Meta Name [Expression]
  | SubscriptedExpr Meta Subscript Expression
  | BytesInExpr Meta Expression
  | BytesInType Meta Type
  | OffsetOf Meta Type Tag
  deriving (Show, Eq, Typeable, Data)

data ExpressionList =
  FunctionCallList Meta Name [Expression]
  | ExpressionList Meta [Expression]
  deriving (Show, Eq, Typeable, Data)

data MonadicOp =
  MonadicSubtr
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
  InCounted Meta Variable Variable
  | InVariable Meta Variable
  deriving (Show, Eq, Typeable, Data)

data OutputItem =
  OutCounted Meta Expression Expression
  | OutExpression Meta Expression
  deriving (Show, Eq, Typeable, Data)

data Replicator = For Meta Name Expression Expression
  deriving (Show, Eq, Typeable, Data)

data Choice = Choice Meta Expression Process
  deriving (Show, Eq, Typeable, Data)

data Alternative =
  Alternative Meta Channel InputMode Process
  | AlternativeCond Meta Expression Channel InputMode Process
  | AlternativeSkip Meta Expression Process
  deriving (Show, Eq, Typeable, Data)

data Option =
  Option Meta [Expression] Process
  | Else Meta Process
  deriving (Show, Eq, Typeable, Data)

data Variant = Variant Meta Tag [InputItem] Process
  deriving (Show, Eq, Typeable, Data)

-- This represents something that can contain local replicators and specifications.
-- (This ought to be a parametric type, "Structured Variant" etc., but doing so
-- makes using generic functions across it hard.)
data Structured =
  Rep Meta Replicator Structured
  | Spec Meta Specification Structured
  | OnlyV Meta Variant
  | OnlyC Meta Choice
  | OnlyO Meta Option
  | OnlyA Meta Alternative
  | Several Meta [Structured]
  deriving (Show, Eq, Typeable, Data)

data InputMode =
  InputSimple Meta [InputItem]
  | InputCase Meta Structured
  | InputAfter Meta Expression
  deriving (Show, Eq, Typeable, Data)

type Formals = [(Type, Name)]
type Specification = (Name, SpecType)
data SpecType =
  Place Meta Expression
  | Declaration Meta Type
  | Is Meta Type Variable
  | ValIs Meta Type Expression
  | DataType Meta Type
  | DataTypeRecord Meta Bool [(Type, Tag)]
  | Protocol Meta [Type]
  | ProtocolCase Meta [(Tag, [Type])]
  | Proc Meta Formals Process
  | Function Meta [Type] Formals ValueProcess
  | Retypes Meta Type Variable
  | Reshapes Meta Type Variable
  | ValRetypes Meta Type Variable
  | ValReshapes Meta Type Variable
  deriving (Show, Eq, Typeable, Data)

data Actual =
  ActualExpression Expression
  | ActualChannel Channel
  deriving (Show, Eq, Typeable, Data)

data ValueProcess =
  ValOfSpec Meta Specification ValueProcess
  | ValOf Meta Process ExpressionList
  deriving (Show, Eq, Typeable, Data)

data ParMode =
  PlainPar | PriPar | PlacedPar
  deriving (Show, Eq, Typeable, Data)

data Process =
  ProcSpec Meta Specification Process
  | Assign Meta [Variable] ExpressionList
  | Input Meta Channel InputMode
  | Output Meta Channel [OutputItem]
  | OutputCase Meta Channel Tag [OutputItem]
  | Skip Meta
  | Stop Meta
  | Main Meta
  | Seq Meta [Process]
  | SeqRep Meta Replicator Process
  | If Meta Structured
  | Case Meta Expression Structured
  | While Meta Expression Process
  | Par Meta ParMode [Process]
  | ParRep Meta ParMode Replicator Process
  | Processor Meta Expression Process
  | Alt Meta Bool Structured
  | ProcCall Meta Name [Actual]
  deriving (Show, Eq, Typeable, Data)

