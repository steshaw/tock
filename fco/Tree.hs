-- occam parse tree
-- This is intended to be imported qualified:
--   import qualified Tree as N

module Tree where

data Node =
-- {{{ BEGIN baseTransformOc
  Decl Node Node
  | Alt [Node]
  | AltRep Node Node
  | PriAlt [Node]
  | PriAltRep Node Node
  | In Node [Node]
-- e.g. InCase (Name "c") [Variant .., Variant ..]
  | Variant Node Node
  | InCase Node [Node]
  | InCaseGuard Node Node [Node]
-- FIXME can turn into InCase ... (Variant .. Skip)
  | InTag Node Node
  | Out Node [Node]
  | OutCase Node Node [Node]
  | ExpList [Node]
  | Assign [Node] Node
  | If [Node]
  | IfRep Node Node
  | InAfter Node Node
  | While Node Node
  | Par [Node]
  | ParRep Node Node
  | PriPar [Node]
  | PriParRep Node Node
  | PlacedPar [Node]
  | PlacedParRep Node Node
  | Processor Node Node
  | Skip
  | Stop
  | Case Node [Node]
  | Seq [Node]
  | SeqRep Node Node
  | ProcCall Node [Node]
  | MainProcess

  | Vars Node [Node]
  | Is Node Node
  | IsType Node Node Node
  | ValIs Node Node
  | ValIsType Node Node Node
  | Place Node Node

  | DataType Node Node
  | Record [Node]
  | PackedRecord [Node]
  | Fields Node [Node]
  | Protocol Node [Node]
  | TaggedProtocol Node [Node]
  | Tag Node [Node]
-- e.g. Proc (Name "out.string") [Formal Int (Name "x"), Formal Bool (Name "y")]
  | Formal Node Node
  | Proc Node [Node] Node
  | Func Node [Node] [Node] Node
  | FuncIs Node [Node] [Node] Node
  | Retypes Node Node Node
  | ValRetypes Node Node Node
  | Reshapes Node Node Node
  | ValReshapes Node Node Node
  | ValOf Node Node

  | Sub Node Node
  | SubFromFor Node Node Node
  | SubFrom Node Node
  | SubFor Node Node

  | CaseExps [Node] Node
  | Else Node

  | For Node Node Node

  | Conv Node Node
  | Round Node Node
  | Trunc Node Node

  | DyadicOp Node Node Node
  | Add
  | Subtr
  | Mul
  | Div
  | Rem
  | Plus
  | Minus
  | Times
  | BitAnd
  | BitOr
  | BitXor
  | And
  | Or
  | Eq
  | NEq
  | Less
  | More
  | LessEq
  | MoreEq
  | After

  | MonadicOp Node Node
  | MonSub
  | MonBitNot
  | MonNot
  | MonSize

  | MostPos Node
  | MostNeg Node
  | Size Node
  | Call Node [Node]
  | BytesIn Node
  | OffsetOf Node Node

  | Guarded Node Node

  | Val Node
  | ChanOf Node
  | PortOf Node
  | Timer
  | Array Node Node
  | ArrayUnsized Node
  | Counted Node Node
  | Bool
  | Byte
  | Int
  | Int16
  | Int32
  | Int64
  | Real32
  | Real64
  | Any

  | TypedLit Node Node
  | LitReal String
  | LitInt String
  | LitHex String
  | LitByte String
  | LitString String
  | LitArray [Node]
  | True
  | False
  | Name String
-- }}} END

-- {{{ BEGIN baseTransformInt
  | IntDecl String Node Node
-- }}} END

-- {{{ BEGIN baseTransformC
  | CCode String
-- }}} END

  deriving (Show, Eq)

