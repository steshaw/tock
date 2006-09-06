-- Source-rewriting passes

module PhaseSource (phaseSource) where

import Tree
import Pass

phaseSource
  = (Phase "Source rewriting"
      [basePass1]
      [
        ("Nuke variable names", nukeVars)
      ])

-- {{{ BEGIN basePass1
basePass1 :: Pass
basePass1 next top node
  = case node of
      OcDecl a b -> OcDecl (top a) (top b)
      OcAlt a -> OcAlt (map top a)
      OcAltRep a b -> OcAltRep (top a) (top b)
      OcPriAlt a -> OcPriAlt (map top a)
      OcPriAltRep a b -> OcPriAltRep (top a) (top b)
      OcIn a b -> OcIn (top a) (map top b)
      OcVariant a b -> OcVariant (top a) (top b)
      OcInCase a b -> OcInCase (top a) (map top b)
      OcInCaseGuard a b c -> OcInCaseGuard (top a) (top b) (map top c)
      OcInTag a b -> OcInTag (top a) (top b)
      OcOut a b -> OcOut (top a) (map top b)
      OcOutCase a b c -> OcOutCase (top a) (top b) (map top c)
      OcExpList a -> OcExpList (map top a)
      OcAssign a b -> OcAssign (map top a) (top b)
      OcIf a -> OcIf (map top a)
      OcIfRep a b -> OcIfRep (top a) (top b)
      OcInAfter a b -> OcInAfter (top a) (top b)
      OcWhile a b -> OcWhile (top a) (top b)
      OcPar a -> OcPar (map top a)
      OcParRep a b -> OcParRep (top a) (top b)
      OcPriPar a -> OcPriPar (map top a)
      OcPriParRep a b -> OcPriParRep (top a) (top b)
      OcPlacedPar a -> OcPlacedPar (map top a)
      OcPlacedParRep a b -> OcPlacedParRep (top a) (top b)
      OcProcessor a b -> OcProcessor (top a) (top b)
      OcSkip -> OcSkip
      OcStop -> OcStop
      OcCase a b -> OcCase (top a) (map top b)
      OcSeq a -> OcSeq (map top a)
      OcSeqRep a b -> OcSeqRep (top a) (top b)
      OcProcCall a b -> OcProcCall (top a) (map top b)
      OcMainProcess -> OcMainProcess
      OcVars a b -> OcVars (top a) (map top b)
      OcIs a b -> OcIs (top a) (top b)
      OcIsType a b c -> OcIsType (top a) (top b) (top c)
      OcValIs a b -> OcValIs (top a) (top b)
      OcValIsType a b c -> OcValIsType (top a) (top b) (top c)
      OcPlace a b -> OcPlace (top a) (top b)
      OcDataType a b -> OcDataType (top a) (top b)
      OcRecord a -> OcRecord (map top a)
      OcPackedRecord a -> OcPackedRecord (map top a)
      OcFields a b -> OcFields (top a) (map top b)
      OcProtocol a b -> OcProtocol (top a) (map top b)
      OcTaggedProtocol a b -> OcTaggedProtocol (top a) (map top b)
      OcTag a b -> OcTag (top a) (map top b)
      OcFormal a b -> OcFormal (top a) (top b)
      OcProc a b c -> OcProc (top a) (map top b) (top c)
      OcFunc a b c d -> OcFunc (top a) (map top b) (map top c) (top d)
      OcFuncIs a b c d -> OcFuncIs (top a) (map top b) (map top c) (top d)
      OcRetypes a b c -> OcRetypes (top a) (top b) (top c)
      OcValRetypes a b c -> OcValRetypes (top a) (top b) (top c)
      OcReshapes a b c -> OcReshapes (top a) (top b) (top c)
      OcValReshapes a b c -> OcValReshapes (top a) (top b) (top c)
      OcValOf a b -> OcValOf (top a) (top b)
      OcSub a b -> OcSub (top a) (top b)
      OcSubFromFor a b c -> OcSubFromFor (top a) (top b) (top c)
      OcSubFrom a b -> OcSubFrom (top a) (top b)
      OcSubFor a b -> OcSubFor (top a) (top b)
      OcCaseExps a b -> OcCaseExps (map top a) (top b)
      OcElse a -> OcElse (top a)
      OcFor a b c -> OcFor (top a) (top b) (top c)
      OcConv a b -> OcConv (top a) (top b)
      OcRound a b -> OcRound (top a) (top b)
      OcTrunc a b -> OcTrunc (top a) (top b)
      OcAdd a b -> OcAdd (top a) (top b)
      OcSubtr a b -> OcSubtr (top a) (top b)
      OcMul a b -> OcMul (top a) (top b)
      OcDiv a b -> OcDiv (top a) (top b)
      OcMod a b -> OcMod (top a) (top b)
      OcRem a b -> OcRem (top a) (top b)
      OcPlus a b -> OcPlus (top a) (top b)
      OcMinus a b -> OcMinus (top a) (top b)
      OcTimes a b -> OcTimes (top a) (top b)
      OcBitAnd a b -> OcBitAnd (top a) (top b)
      OcBitOr a b -> OcBitOr (top a) (top b)
      OcBitXor a b -> OcBitXor (top a) (top b)
      OcAnd a b -> OcAnd (top a) (top b)
      OcOr a b -> OcOr (top a) (top b)
      OcEq a b -> OcEq (top a) (top b)
      OcNEq a b -> OcNEq (top a) (top b)
      OcLess a b -> OcLess (top a) (top b)
      OcMore a b -> OcMore (top a) (top b)
      OcLessEq a b -> OcLessEq (top a) (top b)
      OcMoreEq a b -> OcMoreEq (top a) (top b)
      OcAfter a b -> OcAfter (top a) (top b)
      OcMonSub a -> OcMonSub (top a)
      OcMonBitNot a -> OcMonBitNot (top a)
      OcMonNot a -> OcMonNot (top a)
      OcMostPos a -> OcMostPos (top a)
      OcMostNeg a -> OcMostNeg (top a)
      OcSize a -> OcSize (top a)
      OcCall a b -> OcCall (top a) (map top b)
      OcBytesIn a -> OcBytesIn (top a)
      OcOffsetOf a b -> OcOffsetOf (top a) (top b)
      OcGuarded a b -> OcGuarded (top a) (top b)
      OcVal a -> OcVal (top a)
      OcChanOf a -> OcChanOf (top a)
      OcPortOf a -> OcPortOf (top a)
      OcTimer -> OcTimer
      OcArray a b -> OcArray (top a) (top b)
      OcArrayUnsized a -> OcArrayUnsized (top a)
      OcCounted a b -> OcCounted (top a) (top b)
      OcBool -> OcBool
      OcByte -> OcByte
      OcInt -> OcInt
      OcInt16 -> OcInt16
      OcInt32 -> OcInt32
      OcInt64 -> OcInt64
      OcReal32 -> OcReal32
      OcReal64 -> OcReal64
      OcAny -> OcAny
      OcTypedLit a b -> OcTypedLit (top a) (top b)
      OcLitReal a -> OcLitReal a
      OcLitInt a -> OcLitInt a
      OcLitHex a -> OcLitHex a
      OcLitByte a -> OcLitByte a
      OcLitString a -> OcLitString a
      OcLitArray a -> OcLitArray (map top a)
      OcTrue -> OcTrue
      OcFalse -> OcFalse
      OcName a -> OcName a
      _ -> next node
-- }}} END

nukeVars :: Pass
nukeVars next top node
  = case node of
      OcName n -> OcName "fish"
      _ -> next node

