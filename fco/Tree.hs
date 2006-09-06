-- Tree datatype and operations

module Tree where

data Node =
  OcDecl Node Node
  | OcAlt [Node]
  | OcAltRep Node Node
  | OcPriAlt [Node]
  | OcPriAltRep Node Node
  | OcIn Node [Node]
-- e.g. OcInCase (OcName "c") [OcVariant .., OcVariant ..]
  | OcVariant Node Node
  | OcInCase Node [Node]
  | OcInCaseGuard Node Node [Node]
-- FIXME can turn into OcInCase ... (OcVariant .. OcSkip)
  | OcInTag Node Node
  | OcOut Node [Node]
  | OcOutCase Node Node [Node]
  | OcExpList [Node]
  | OcAssign [Node] Node
  | OcIf [Node]
  | OcIfRep Node Node
  | OcInAfter Node Node
  | OcWhile Node Node
  | OcPar [Node]
  | OcParRep Node Node
  | OcPriPar [Node]
  | OcPriParRep Node Node
  | OcPlacedPar [Node]
  | OcPlacedParRep Node Node
  | OcProcessor Node Node
  | OcSkip
  | OcStop
  | OcCase Node [Node]
  | OcSeq [Node]
  | OcSeqRep Node Node
  | OcProcCall Node [Node]
  | OcMainProcess

  | OcVars Node [Node]
  | OcIs Node Node
  | OcIsType Node Node Node
  | OcValIs Node Node
  | OcValIsType Node Node Node
  | OcPlace Node Node

  | OcDataType Node Node
  | OcRecord [Node]
  | OcPackedRecord [Node]
  | OcFields Node [Node]
  | OcProtocol Node [Node]
  | OcTaggedProtocol Node [Node]
  | OcTag Node [Node]
-- e.g. OcProc (OcName "out.string") [OcFormal OcInt (OcName "x"), OcFormal OcBool (OcName "y")]
  | OcFormal Node Node
  | OcProc Node [Node] Node
  | OcFunc Node [Node] [Node] Node
  | OcFuncIs Node [Node] [Node] Node
  | OcRetypes Node Node Node
  | OcValRetypes Node Node Node
  | OcReshapes Node Node Node
  | OcValReshapes Node Node Node
  | OcValOf Node Node

  | OcSub Node Node
  | OcSubFromFor Node Node Node
  | OcSubFrom Node Node
  | OcSubFor Node Node

  | OcCaseExps [Node] Node
  | OcElse Node

  | OcFor Node Node Node

  | OcConv Node Node
  | OcRound Node Node
  | OcTrunc Node Node
  | OcAdd Node Node
  | OcSubtr Node Node
  | OcMul Node Node
  | OcDiv Node Node
  | OcMod Node Node
  | OcRem Node Node
  | OcPlus Node Node
  | OcMinus Node Node
  | OcTimes Node Node
  | OcBitAnd Node Node
  | OcBitOr Node Node
  | OcBitXor Node Node
  | OcAnd Node Node
  | OcOr Node Node
  | OcEq Node Node
  | OcNEq Node Node
  | OcLess Node Node
  | OcMore Node Node
  | OcLessEq Node Node
  | OcMoreEq Node Node
  | OcAfter Node Node
  | OcMonSub Node
  | OcMonBitNot Node
  | OcMonNot Node
  | OcMostPos Node
  | OcMostNeg Node
  | OcSize Node
  | OcCall Node [Node]
  | OcBytesIn Node
  | OcOffsetOf Node Node

  | OcGuarded Node Node

  | OcVal Node
  | OcChanOf Node
  | OcPortOf Node
  | OcTimer
  | OcArray Node Node
  | OcArrayUnsized Node
  | OcCounted Node Node
  | OcBool
  | OcByte
  | OcInt
  | OcInt16
  | OcInt32
  | OcInt64
  | OcReal32
  | OcReal64
  | OcAny

  | OcTypedLit Node Node
  | OcLitReal String
  | OcLitInt String
  | OcLitHex String
  | OcLitByte String
  | OcLitString String
  | OcLitArray [Node]
  | OcTrue
  | OcFalse
  | OcName String

  deriving (Show, Eq)

