-- Lisp-style s-expression support

module SExpression where

import List
import Tree

data SExp = Item String | List [SExp]

instance Show SExp where
  show (Item s) = s
  show (List is) = "(" ++ (concat $ intersperse " " $ map show is) ++ ")"

nodeToSExp :: Node -> SExp
nodeToSExp node
  = case node of
      OcDecl a b -> wrap2 "decl" (top a) (top b)
      OcAlt a -> wrapl "alt" (map top a)
      OcAltRep a b -> wrap2 "alt-rep" (top a) (top b)
      OcPriAlt a -> wrapl "pri-alt" (map top a)
      OcPriAltRep a b -> wrap2 "pri-alt-rep" (top a) (top b)
      OcIn a b -> wrapl1 "?" (top a) (map top b)
      OcVariant a b -> wrap2 "variant" (top a) (top b)
      OcInCase a b -> wrapl1 "?case" (top a) (map top b)
      OcInCaseGuard a b c -> wrapl2 "?case-guard" (top a) (top b) (map top c)
      OcInTag a b -> wrap2 "?tag" (top a) (top b)
      OcOut a b -> wrapl1 "!" (top a) (map top b)
      OcOutCase a b c -> wrapl2 "!case" (top a) (top b) (map top c)
      OcExpList a -> wrapl "exp-list" (map top a)
      OcAssign a b -> wrap2 ":=" (List $ map top a) (top b)
      OcIf a -> wrapl "if" (map top a)
      OcIfRep a b -> wrap2 "if-rep" (top a) (top b)
      OcInAfter a b -> wrap2 "?after" (top a) (top b)
      OcWhile a b -> wrap2 "while" (top a) (top b)
      OcPar a -> wrapl "par" (map top a)
      OcParRep a b -> wrap2 "par-rep" (top a) (top b)
      OcPriPar a -> wrapl "pri-par" (map top a)
      OcPriParRep a b -> wrap2 "pri-par-rep" (top a) (top b)
      OcPlacedPar a -> wrapl "placed-par" (map top a)
      OcPlacedParRep a b -> wrap2 "placed-par-rep" (top a) (top b)
      OcProcessor a b -> wrap2 "processor" (top a) (top b)
      OcSkip -> Item "skip"
      OcStop -> Item "stop"
      OcCase a b -> wrapl1 "case" (top a) (map top b)
      OcSeq a -> wrapl "seq" (map top a)
      OcSeqRep a b -> wrap2 "seq-rep" (top a) (top b)
      OcProcCall a b -> wrapl1 "proc-call" (top a) (map top b)
      OcMainProcess -> Item "main"
      OcVars a b -> wrapl1 "vars" (top a) (map top b)
      OcIs a b -> wrap2 "is" (top a) (top b)
      OcIsType a b c -> wrap3 "is-type" (top a) (top b) (top c)
      OcValIs a b -> wrap2 "val-is" (top a) (top b)
      OcValIsType a b c -> wrap3 "val-is-type" (top a) (top b) (top c)
      OcPlace a b -> wrap2 "place" (top a) (top b)
      OcDataType a b -> wrap2 "data-type" (top a) (top b)
      OcRecord a -> wrapl "record" (map top a)
      OcPackedRecord a -> wrapl "packed-record" (map top a)
      OcFields a b -> wrapl1 "fields" (top a) (map top b)
      OcProtocol a b -> wrapl1 "protocol" (top a) (map top b)
      OcTaggedProtocol a b -> wrapl1 "tagged-protocol" (top a) (map top b)
      OcTag a b -> wrapl1 "tag" (top a) (map top b)
      OcFormal a b -> wrap2 "formal" (top a) (top b)
      OcProc a b c -> wrap3 "proc" (top a) (List $ map top b) (top c)
      OcFunc a b c d -> wrap4 "func" (top a) (List $ map top b) (List $ map top c) (top d)
      OcFuncIs a b c d -> wrap4 "func-is" (top a) (List $ map top b) (List $ map top c) (top d)
      OcRetypes a b c -> wrap3 "retypes" (top a) (top b) (top c)
      OcValRetypes a b c -> wrap3 "val-retypes" (top a) (top b) (top c)
      OcReshapes a b c -> wrap3 "reshapes" (top a) (top b) (top c)
      OcValReshapes a b c -> wrap3 "val-reshapes" (top a) (top b) (top c)
      OcValOf a b -> wrap2 "valof" (top a) (top b)
      OcSub a b -> wrap2 "sub" (top a) (top b)
      OcSubFromFor a b c -> wrap3 "sub-from-for" (top a) (top b) (top c)
      OcSubFrom a b -> wrap2 "sub-from" (top a) (top b)
      OcSubFor a b -> wrap2 "sub-for" (top a) (top b)
      OcCaseExps a b -> wrap2 "case-exps" (List $ map top a) (top b)
      OcElse a -> wrap "else" (top a)
      OcFor a b c -> wrap3 "for" (top a) (top b) (top c)
      OcConv a b -> wrap2 "conv" (top a) (top b)
      OcRound a b -> wrap2 "round" (top a) (top b)
      OcTrunc a b -> wrap2 "trunc" (top a) (top b)
      OcAdd a b -> wrap2 "+" (top a) (top b)
      OcSubtr a b -> wrap2 "-" (top a) (top b)
      OcMul a b -> wrap2 "*" (top a) (top b)
      OcDiv a b -> wrap2 "/" (top a) (top b)
      OcRem a b -> wrap2 "\\" (top a) (top b)
      OcPlus a b -> wrap2 "plus" (top a) (top b)
      OcMinus a b -> wrap2 "minus" (top a) (top b)
      OcTimes a b -> wrap2 "times" (top a) (top b)
      OcBitAnd a b -> wrap2 "bitand" (top a) (top b)
      OcBitOr a b -> wrap2 "bitor" (top a) (top b)
      OcBitXor a b -> wrap2 "bitxor" (top a) (top b)
      OcAnd a b -> wrap2 "and" (top a) (top b)
      OcOr a b -> wrap2 "or" (top a) (top b)
      OcEq a b -> wrap2 "=" (top a) (top b)
      OcNEq a b -> wrap2 "<>" (top a) (top b)
      OcLess a b -> wrap2 "<" (top a) (top b)
      OcMore a b -> wrap2 ">" (top a) (top b)
      OcLessEq a b -> wrap2 "<=" (top a) (top b)
      OcMoreEq a b -> wrap2 ">=" (top a) (top b)
      OcAfter a b -> wrap2 "after" (top a) (top b)
      OcMonSub a -> wrap "-" (top a)
      OcMonBitNot a -> wrap "bitnot" (top a)
      OcMonNot a -> wrap "not" (top a)
      OcMostPos a -> wrap "mostpos" (top a)
      OcMostNeg a -> wrap "mostneg" (top a)
      OcSize a -> wrap "size" (top a)
      OcCall a b -> wrapl1 "call" (top a) (map top b)
      OcBytesIn a -> wrap "bytesin" (top a)
      OcOffsetOf a b -> wrap2 "offsetof" (top a) (top b)
      OcGuarded a b -> wrap2 "guarded" (top a) (top b)
      OcVal a -> wrap "val" (top a)
      OcChanOf a -> wrap "chan" (top a)
      OcPortOf a -> wrap "port" (top a)
      OcTimer -> Item "timer"
      OcArray a b -> wrap2 "array" (top a) (top b)
      OcArrayUnsized a -> wrap "array-unsized" (top a)
      OcCounted a b -> wrap2 "counted" (top a) (top b)
      OcBool -> Item "bool"
      OcByte -> Item "byte"
      OcInt -> Item "int"
      OcInt16 -> Item "int16"
      OcInt32 -> Item "int32"
      OcInt64 -> Item "int64"
      OcReal32 -> Item "real32"
      OcReal64 -> Item "real64"
      OcAny -> Item "any"
      OcTypedLit a b -> wrap2 "typed-literal" (top a) (top b)
      OcLitReal a -> wrap "real-literal" (Item a)
      OcLitInt a -> wrap "integer-literal" (Item a)
      OcLitHex a -> wrap "hex-literal" (Item a)
      OcLitByte a -> wrap "byte-literal" (Item a)
      OcLitString a -> wrap "string-literal" (Item a)
      OcLitArray a -> wrapl "array-literal" (map top a)
      OcTrue -> Item "true"
      OcFalse -> Item "false"
      OcName a -> wrap "name" (Item a)
      _ -> error $ "Unsupported node: " ++ (show node)
    where top = nodeToSExp
          wrap name arg = List [Item name, arg]
          wrap2 name arg1 arg2 = List [Item name, arg1, arg2]
          wrap3 name arg1 arg2 arg3 = List [Item name, arg1, arg2, arg3]
          wrap4 name arg1 arg2 arg3 arg4 = List [Item name, arg1, arg2, arg3, arg4]
          wrapl name args = List ((Item name) : args)
          wrapl1 name arg1 args = List ((Item name) : arg1 : args)
          wrapl2 name arg1 arg2 args = List ((Item name) : arg1 : arg2 : args)

