-- Lisp-style s-expression support

module SExpression where

import List
import qualified PT as N

data SExp = Item String | List [SExp]

instance Show SExp where
  show (Item s) = s
  show (List is) = "(" ++ (concat $ intersperse " " $ map show is) ++ ")"

dyadicName :: N.Node -> String
dyadicName n = case n of
  N.Add -> "+"
  N.Subtr -> "-"
  N.Mul -> "*"
  N.Div -> "/"
  N.Rem -> "mod"
  N.Plus -> "plus"
  N.Minus -> "minus"
  N.Times -> "times"
  N.BitAnd -> "bitand"
  N.BitOr -> "bitor"
  N.BitXor -> "bitxor"
  N.And -> "and"
  N.Or -> "or"
  N.Eq -> "="
  N.NEq -> "<>"
  N.Less -> "<"
  N.More -> ">"
  N.LessEq -> "<="
  N.MoreEq -> ">="
  N.After -> "after"

monadicName :: N.Node -> String
monadicName n = case n of
  N.MonSub -> "-"
  N.MonBitNot -> "bitnot"
  N.MonNot -> "not"
  N.MonSize -> "size"

nodeToSExp :: N.Node -> SExp
nodeToSExp node
  = case node of
      N.Decl a b -> wrap2 ":" (top a) (top b)
      N.Alt a -> wrapl "alt" (map top a)
      N.AltRep a b -> wrap2 "alt-rep" (top a) (top b)
      N.PriAlt a -> wrapl "pri-alt" (map top a)
      N.PriAltRep a b -> wrap2 "pri-alt-rep" (top a) (top b)
      N.In a (N.InSimple b) -> wrapl1 "?" (top a) (map top b)
      N.Variant a b -> wrap2 "variant" (top a) (top b)
      N.In a (N.InCase b) -> wrapl1 "?case" (top a) (map top b)
      N.In a (N.InTag b) -> wrap2 "?case-tag" (top a) (top b)
      N.In a (N.InAfter b) -> wrap2 "?after" (top a) (top b)
      N.Out a b -> wrapl1 "!" (top a) (map top b)
      N.OutCase a b c -> wrapl2 "!case" (top a) (top b) (map top c)
      N.ExpList a -> wrapl "exp-list" (map top a)
      N.Assign a b -> wrap2 ":=" (List $ map top a) (top b)
      N.If a -> wrapl "if" (map top a)
      N.IfRep a b -> wrap2 "if-rep" (top a) (top b)
      N.While a b -> wrap2 "while" (top a) (top b)
      N.Par a -> wrapl "par" (map top a)
      N.ParRep a b -> wrap2 "par-rep" (top a) (top b)
      N.PriPar a -> wrapl "pri-par" (map top a)
      N.PriParRep a b -> wrap2 "pri-par-rep" (top a) (top b)
      N.PlacedPar a -> wrapl "placed-par" (map top a)
      N.PlacedParRep a b -> wrap2 "placed-par-rep" (top a) (top b)
      N.Processor a b -> wrap2 "processor" (top a) (top b)
      N.Skip -> Item "skip"
      N.Stop -> Item "stop"
      N.Case a b -> wrapl1 "case" (top a) (map top b)
      N.Seq a -> wrapl "seq" (map top a)
      N.SeqRep a b -> wrap2 "seq-rep" (top a) (top b)
      N.ProcCall a b -> wrapl1 "proc-call" (top a) (map top b)
      N.MainProcess -> Item "main"
      N.Vars a b -> wrapl1 "vars" (top a) (map top b)
      N.Is a b -> wrap2 "is" (top a) (top b)
      N.IsType a b c -> wrap3 "is-type" (top a) (top b) (top c)
      N.ValIs a b -> wrap2 "val-is" (top a) (top b)
      N.ValIsType a b c -> wrap3 "val-is-type" (top a) (top b) (top c)
      N.Place a b -> wrap2 "place-at" (top a) (top b)
      N.DataType a b -> wrap2 "data-type" (top a) (top b)
      N.Record a -> wrapl "record" (map top a)
      N.PackedRecord a -> wrapl "packed-record" (map top a)
      N.Fields a b -> wrapl1 "fields" (top a) (map top b)
      N.Protocol a b -> wrapl1 "protocol" (top a) (map top b)
      N.TaggedProtocol a b -> wrapl1 "protocol-tagged" (top a) (map top b)
      N.Tag a b -> wrapl1 "tag" (top a) (map top b)
      N.Formals a b -> wrapl1 "formal" (top a) (map top b)
      N.Proc a b c -> wrap3 "proc" (top a) (List $ map top b) (top c)
      N.Func a b c d -> wrap4 "function" (top a) (List $ map top b) (List $ map top c) (top d)
      N.FuncIs a b c d -> wrap4 "function-is" (top a) (List $ map top b) (List $ map top c) (top d)
      N.Retypes a b c -> wrap3 "retypes" (top a) (top b) (top c)
      N.ValRetypes a b c -> wrap3 "val-retypes" (top a) (top b) (top c)
      N.Reshapes a b c -> wrap3 "reshapes" (top a) (top b) (top c)
      N.ValReshapes a b c -> wrap3 "val-reshapes" (top a) (top b) (top c)
      N.ValOf a b -> wrap2 "valof" (top a) (top b)
      N.Sub (N.SubPlain b) a -> wrap2 "sub" (top a) (top b)
      N.Sub (N.SubFromFor b c) a -> wrap3 "sub-from-for" (top a) (top b) (top c)
      N.Sub (N.SubFrom b) a -> wrap2 "sub-from" (top a) (top b)
      N.Sub (N.SubFor b) a -> wrap2 "sub-for" (top a) (top b)
      N.CaseExps a b -> wrap2 "case-exps" (List $ map top a) (top b)
      N.Else a -> wrap "else" (top a)
      N.For a b c -> wrap3 "for" (top a) (top b) (top c)
      N.Conv a b -> wrap2 "conv" (top a) (top b)
      N.Round a b -> wrap2 "round" (top a) (top b)
      N.Trunc a b -> wrap2 "trunc" (top a) (top b)
      N.DyadicOp o a b -> wrap2 (dyadicName o) (top a) (top b)
      N.MonadicOp o a -> wrap (monadicName o) (top a)
      N.MostPos a -> wrap "mostpos" (top a)
      N.MostNeg a -> wrap "mostneg" (top a)
      N.Size a -> wrap "size" (top a)
      N.Call a b -> wrapl1 "call" (top a) (map top b)
      N.BytesIn a -> wrap "bytesin" (top a)
      N.OffsetOf a b -> wrap2 "offsetof" (top a) (top b)
      N.Guard a b -> wrap2 "guard" (top a) (top b)
      N.CondGuard a b -> wrap2 "cond" (top a) (top b)
      N.Choice a b -> wrap2 "choice" (top a) (top b)
      N.Val a -> wrap "val" (top a)
      N.ChanOf a -> wrap "chan" (top a)
      N.PortOf a -> wrap "port" (top a)
      N.Timer -> Item "timer"
      N.Array a b -> wrap2 "array" (top a) (top b)
      N.ArrayUnsized a -> wrap "array-unsized" (top a)
      N.Counted a b -> wrap2 "::" (top a) (top b)
      N.Bool -> Item "bool"
      N.Byte -> Item "byte"
      N.Int -> Item "int"
      N.Int16 -> Item "int16"
      N.Int32 -> Item "int32"
      N.Int64 -> Item "int64"
      N.Real32 -> Item "real32"
      N.Real64 -> Item "real64"
      N.Any -> Item "any"
      N.TypedLit a b -> wrap2 "typed-literal" (top a) (top b)
      N.LitReal a -> wrap "real-literal" (Item a)
      N.LitInt a -> wrap "integer-literal" (Item a)
      N.LitHex a -> wrap "hex-literal" (Item a)
      N.LitByte a -> wrap "byte-literal" (Item ("'" ++ a ++ "'"))
      N.LitString a -> wrap "string-literal" (Item ("\"" ++ a ++ "\""))
      N.LitArray a -> wrapl "array-literal" (map top a)
      N.True -> Item "true"
      N.False -> Item "false"
      N.Name a -> wrap "name" (Item a)
      _ -> error $ "Unsupported node: " ++ (show node)
    where top = nodeToSExp
          wrap name arg = List [Item name, arg]
          wrap2 name arg1 arg2 = List [Item name, arg1, arg2]
          wrap3 name arg1 arg2 arg3 = List [Item name, arg1, arg2, arg3]
          wrap4 name arg1 arg2 arg3 arg4 = List [Item name, arg1, arg2, arg3, arg4]
          wrapl name args = List ((Item name) : args)
          wrapl1 name arg1 args = List ((Item name) : arg1 : args)
          wrapl2 name arg1 arg2 args = List ((Item name) : arg1 : arg2 : args)

nodeToSOccam :: N.Node -> SExp
nodeToSOccam node
  = case node of
      N.Decl a b -> wrap2 ":" (top a) (top b)
      N.Alt a -> wrapl "alt" (map top a)
      N.AltRep a b -> wrap2 "alt" (top a) (top b)
      N.PriAlt a -> wrapl "pri-alt" (map top a)
      N.PriAltRep a b -> wrap2 "pri-alt" (top a) (top b)
      N.In a (N.InSimple b) -> wrapl1 "?" (top a) (map top b)
      N.Variant a b -> wrap2 "variant" (top a) (top b)
      N.In a (N.InCase b) -> wrapl1 "?case" (top a) (map top b)
      N.In a (N.InTag b) -> wrap2 "?case-tag" (top a) (top b)
      N.In a (N.InAfter b) -> wrap2 "?after" (top a) (top b)
      N.Out a b -> wrapl1 "!" (top a) (map top b)
      N.OutCase a b c -> wrapl2 "!case" (top a) (top b) (map top c)
      N.ExpList a -> List (map top a)
      N.Assign a b -> wrap2 ":=" (List $ map top a) (top b)
      N.If a -> wrapl "if" (map top a)
      N.IfRep a b -> wrap2 "if" (top a) (top b)
      N.While a b -> wrap2 "while" (top a) (top b)
      N.Par a -> wrapl "par" (map top a)
      N.ParRep a b -> wrap2 "par" (top a) (top b)
      N.PriPar a -> wrapl "pri-par" (map top a)
      N.PriParRep a b -> wrap2 "pri-par" (top a) (top b)
      N.PlacedPar a -> wrapl "placed-par" (map top a)
      N.PlacedParRep a b -> wrap2 "placed-par" (top a) (top b)
      N.Processor a b -> wrap2 "processor" (top a) (top b)
      N.Skip -> Item "skip"
      N.Stop -> Item "stop"
      N.Case a b -> wrapl1 "case" (top a) (map top b)
      N.Seq a -> wrapl "seq" (map top a)
      N.SeqRep a b -> wrap2 "seq" (top a) (top b)
      N.ProcCall a b -> List ((top a) : (map top b))
      N.MainProcess -> Item "main"
      N.Vars a b -> List ((top a) : (map top b))
      N.Is a b -> wrap2 "is" (top a) (top b)
      N.IsType a b c -> wrap3 "is" (top a) (top b) (top c)
      N.ValIs a b -> wrap2 "val-is" (top a) (top b)
      N.ValIsType a b c -> wrap3 "val-is" (top a) (top b) (top c)
      N.Place a b -> wrap2 "place-at" (top a) (top b)
      N.DataType a b -> wrap2 "data-type" (top a) (top b)
      N.Record a -> wrapl "record" (map top a)
      N.PackedRecord a -> wrapl "packed-record" (map top a)
      N.Fields a b -> List ((top a) : (map top b))
      N.Protocol a b -> wrapl1 "protocol" (top a) (map top b)
      N.TaggedProtocol a b -> wrapl1 "protocol" (top a) (map top b)
      N.Tag a b -> List ((top a) : (map top b))
      N.Formals a b -> List ((top a) : (map top b))
      N.Proc a b c -> wrap3 "proc" (top a) (List $ map top b) (top c)
      N.Func a b c d -> wrap4 "function" (top a) (List $ map top b) (List $ map top c) (top d)
      N.FuncIs a b c d -> wrap4 "function-is" (top a) (List $ map top b) (List $ map top c) (top d)
      N.Retypes a b c -> wrap3 "retypes" (top a) (top b) (top c)
      N.ValRetypes a b c -> wrap3 "val-retypes" (top a) (top b) (top c)
      N.Reshapes a b c -> wrap3 "reshapes" (top a) (top b) (top c)
      N.ValReshapes a b c -> wrap3 "val-reshapes" (top a) (top b) (top c)
      N.ValOf a b -> wrap2 "valof" (top a) (top b)
      N.Sub (N.SubPlain b) a -> wrap2 "sub" (top a) (top b)
      N.Sub (N.SubFromFor b c) a -> wrap3 "sub-from-for" (top a) (top b) (top c)
      N.Sub (N.SubFrom b) a -> wrap2 "sub-from" (top a) (top b)
      N.Sub (N.SubFor b) a -> wrap2 "sub-for" (top a) (top b)
      N.CaseExps a b -> l2 (List $ map top a) (top b)
      N.Else a -> wrap "else" (top a)
      N.For a b c -> wrap3 "for" (top a) (top b) (top c)
      N.Conv a b -> wrap2 "conv" (top a) (top b)
      N.Round a b -> wrap2 "round" (top a) (top b)
      N.Trunc a b -> wrap2 "trunc" (top a) (top b)
      N.DyadicOp o a b -> wrap2 (dyadicName o) (top a) (top b)
      N.MonadicOp o a -> wrap (monadicName o) (top a)
      N.MostPos a -> wrap "mostpos" (top a)
      N.MostNeg a -> wrap "mostneg" (top a)
      N.Size a -> wrap "size" (top a)
      N.Call a b -> wrapl1 "call" (top a) (map top b)
      N.BytesIn a -> wrap "bytesin" (top a)
      N.OffsetOf a b -> wrap2 "offsetof" (top a) (top b)
      N.Guard a b -> List [top a, top b]
      N.CondGuard a b -> wrap2 "cond" (top a) (top b)
      N.Choice a b -> List [top a, top b]
      N.Val a -> wrap "val" (top a)
      N.ChanOf a -> wrap "chan" (top a)
      N.PortOf a -> wrap "port" (top a)
      N.Timer -> Item "timer"
      N.Array a b -> wrap2 "array" (top a) (top b)
      N.ArrayUnsized a -> wrap "array" (top a)
      N.Counted a b -> wrap2 "::" (top a) (top b)
      N.Bool -> Item "bool"
      N.Byte -> Item "byte"
      N.Int -> Item "int"
      N.Int16 -> Item "int16"
      N.Int32 -> Item "int32"
      N.Int64 -> Item "int64"
      N.Real32 -> Item "real32"
      N.Real64 -> Item "real64"
      N.Any -> Item "any"
      N.TypedLit a b -> l2 (top a) (top b)
      N.LitReal a -> Item a
      N.LitInt a -> Item a
      N.LitHex a -> Item a
      N.LitByte a -> Item ("'" ++ a ++ "'")
      N.LitString a -> Item ("\"" ++ a ++ "\"")
      N.LitArray a -> List (map top a)
      N.True -> Item "true"
      N.False -> Item "false"
      N.Name a -> Item a
      _ -> error $ "Unsupported node: " ++ (show node)
    where top = nodeToSOccam
          wrap name arg = List [Item name, arg]
          wrap2 name arg1 arg2 = List [Item name, arg1, arg2]
          wrap3 name arg1 arg2 arg3 = List [Item name, arg1, arg2, arg3]
          wrap4 name arg1 arg2 arg3 arg4 = List [Item name, arg1, arg2, arg3, arg4]
          wrapl name args = List ((Item name) : args)
          wrapl1 name arg1 args = List ((Item name) : arg1 : args)
          wrapl2 name arg1 arg2 args = List ((Item name) : arg1 : arg2 : args)
          l2 arg1 arg2 = List [arg1, arg2]

