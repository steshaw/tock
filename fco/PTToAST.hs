-- Convert the parse tree into the AST

module PTToAST (ptToAST) where

import qualified PT as N
import qualified AST as O

doName :: N.Node -> O.Name
doName (N.Node _ (N.Name s)) = O.Name s
doName n = error $ "Failed to translate to Name: " ++ (show n)

doTag :: N.Node -> O.Tag
doTag (N.Node _ (N.Name s)) = O.Tag s

doType :: N.Node -> O.Type
doType n@(N.Node _ nt) = case nt of
  N.Bool -> O.Bool
  N.Byte -> O.Byte
  N.Int -> O.Int
  N.Int16 -> O.Int16
  N.Int32 -> O.Int32
  N.Int64 -> O.Int64
  N.Real32 -> O.Real32
  N.Real64 -> O.Real64
  N.Array e t -> O.Array (doExpression e) (doType t)
  N.ArrayUnsized t -> O.ArrayUnsized (doType t)
  N.Name _ -> O.UserType (doName n)
  N.ChanOf t -> O.Chan (doType t)
  N.Counted ct dt -> O.Counted (doType ct) (doType dt)
  N.Any -> O.Any
  N.Timer -> O.Timer
  N.PortOf t -> O.Port (doType t)
  N.Val t -> O.Val (doType t)

doMonadicOp :: N.Node -> O.MonadicOp
doMonadicOp n@(N.Node _ nt) = case nt of
  N.MonSub -> O.MonadicSubtr
  N.MonBitNot -> O.MonadicBitNot
  N.MonNot -> O.MonadicNot
  N.MonSize -> O.MonadicSize

doDyadicOp :: N.Node -> O.DyadicOp
doDyadicOp n@(N.Node _ nt) = case nt of
  N.Add -> O.Add
  N.Subtr -> O.Subtr
  N.Mul -> O.Mul
  N.Div -> O.Div
  N.Rem -> O.Rem
  N.Plus -> O.Plus
  N.Minus -> O.Minus
  N.Times -> O.Times
  N.BitAnd -> O.BitAnd
  N.BitOr -> O.BitOr
  N.BitXor -> O.BitXor
  N.And -> O.And
  N.Or -> O.Or
  N.Eq -> O.Eq
  N.NEq -> O.NotEq
  N.Less -> O.Less
  N.More -> O.More
  N.LessEq -> O.LessEq
  N.MoreEq -> O.MoreEq
  N.After -> O.After

doSubscript :: N.Node -> O.Subscript
doSubscript n@(N.Node _ nt) = case nt of
  N.SubPlain e -> O.Subscript (doExpression e)
  N.SubFromFor e f -> O.SubFromFor (doExpression e) (doExpression f)
  N.SubFrom e -> O.SubFrom (doExpression e)
  N.SubFor f -> O.SubFor (doExpression f)

doLiteral :: N.Node -> O.Literal
doLiteral n@(N.Node _ nt) = case nt of
  N.TypedLit t l -> O.Literal (doType t) rep where (O.Literal _ rep) = doLiteral l
  N.LitReal s -> O.Literal O.Real32 (O.RealLiteral s)
  N.LitInt s -> O.Literal O.Int (O.IntLiteral s)
  N.LitHex s -> O.Literal O.Int (O.HexLiteral s)
  N.LitByte s -> O.Literal O.Byte (O.ByteLiteral s)
  N.LitString s -> O.Literal (O.ArrayUnsized O.Byte) (O.StringLiteral s)
  N.LitArray ns -> O.Literal O.Infer (O.ArrayLiteral (map doExpression ns))
  N.Sub s l -> O.SubscriptedLiteral (doSubscript s) (doLiteral l)

doVariable :: N.Node -> O.Variable
doVariable n@(N.Node _ nt) = case nt of
  N.Name _ -> O.Variable (doName n)
  N.Sub s v -> O.SubscriptedVariable (doSubscript s) (doVariable v)
  _ -> error $ "Failed to translate to Variable: " ++ (show n)

doExpression :: N.Node -> O.Expression
doExpression n@(N.Node _ nt) = case nt of
  N.MonadicOp o a -> O.Monadic (doMonadicOp o) (doExpression a)
  N.DyadicOp o a b -> O.Dyadic (doDyadicOp o) (doExpression a) (doExpression b)
  N.MostPos t -> O.MostPos (doType t)
  N.MostNeg t -> O.MostNeg (doType t)
  N.Size t -> O.Size (doType t)
  N.Conv t e -> O.Conversion O.DefaultConversion (doType t) (doExpression e)
  N.Round t e -> O.Conversion O.Round (doType t) (doExpression e)
  N.Trunc t e -> O.Conversion O.Trunc (doType t) (doExpression e)
  N.TypedLit _ _ -> O.ExprLiteral $ doLiteral n
  N.LitReal _ -> O.ExprLiteral $ doLiteral n
  N.LitInt _ -> O.ExprLiteral $ doLiteral n
  N.LitHex _ -> O.ExprLiteral $ doLiteral n
  N.LitByte _ -> O.ExprLiteral $ doLiteral n
  N.LitString _ -> O.ExprLiteral $ doLiteral n
  N.LitArray _ -> O.ExprLiteral $ doLiteral n
  N.True -> O.True
  N.False -> O.False
  N.Call f es -> O.FunctionCall (doName f) (map doExpression es)
  N.BytesIn t -> O.BytesInType (doType t)
  N.OffsetOf t g -> O.OffsetOf (doType t) (doTag g)
  otherwise -> O.ExprVariable (doVariable n)

doExpressionList :: N.Node -> O.ExpressionList
doExpressionList n@(N.Node _ nt) = case nt of
  N.Call f es -> O.FunctionCallList (doName f) (map doExpression es)
  N.ExpList es -> O.ExpressionList (map doExpression es)

doReplicator :: N.Node -> O.Replicator
doReplicator n@(N.Node _ nt) = case nt of
  N.For v f t -> O.For (doName v) (doExpression f) (doExpression t)

doFields :: [N.Node] -> [(O.Type, O.Tag)]
doFields ns = concat $ [[(doType t, doTag f) | f <- fs] | (N.Node _ (N.Fields t fs)) <- ns]

doFormals :: [N.Node] -> [(O.Type, O.Name)]
doFormals fs = concat $ [[(doType t, doName n) | n <- ns] | (N.Node _ (N.Formals t ns)) <- fs]

doVariant :: N.Node -> O.Structured O.Variant
doVariant n@(N.Node _ nt) = case nt of
  N.Variant (N.Node _ (N.Tag t is)) p -> O.Only $ O.Variant (doTag t) (map doInputItem is) (doProcess p)
  N.Decl s v -> doSpecifications s O.Spec (doVariant v)

doChoice :: N.Node -> O.Structured O.Choice
doChoice n@(N.Node _ nt) = case nt of
  N.If cs -> O.Several $ map doChoice cs
  N.IfRep r c -> O.Rep (doReplicator r) (doChoice c)
  N.Choice b p -> O.Only $ O.Choice (doExpression b) (doProcess p)
  N.Decl s c -> doSpecifications s O.Spec (doChoice c)

doOption :: N.Node -> O.Structured O.Option
doOption n@(N.Node _ nt) = case nt of
  N.CaseExps cs p -> O.Only $ O.Option (map doExpression cs) (doProcess p)
  N.Else p -> O.Only $ O.Else (doProcess p)
  N.Decl s o -> doSpecifications s O.Spec (doOption o)

doInputItem :: N.Node -> O.InputItem
doInputItem n@(N.Node _ nt) = case nt of
  N.Counted c d -> O.InCounted (doVariable c) (doVariable d)
  otherwise -> O.InVariable (doVariable n)

doOutputItem :: N.Node -> O.OutputItem
doOutputItem n@(N.Node _ nt) = case nt of
  N.Counted c d -> O.OutCounted (doExpression c) (doExpression d)
  otherwise -> O.OutExpression (doExpression n)

doInputMode :: N.Node -> O.InputMode
doInputMode n@(N.Node _ nt) = case nt of
  N.InSimple is -> O.InputSimple (map doInputItem is)
  N.InCase vs -> O.InputCase (O.Several $ map doVariant vs)
  N.InTag (N.Node _ (N.Tag t is)) -> O.InputCase (O.Only $ O.Variant (doTag t) (map doInputItem is) O.Skip)
  N.InAfter e -> O.InputAfter (doExpression e)

doSimpleSpec :: N.Node -> O.Specification
doSimpleSpec n@(N.Node _ nt) = case nt of
  N.Is d v -> (doName d, O.Is O.Infer (doVariable v))
  N.IsType t d v -> (doName d, O.Is (doType t) (doVariable v))
  N.ValIs d e -> (doName d, O.ValIs O.Infer (doExpression e))
  N.ValIsType t d e -> (doName d, O.ValIs (doType t) (doExpression e))
  N.Place v e -> (doName v, O.Place (doExpression e))
  N.DataType n (N.Node _ (N.Record fs)) -> (doName n, O.DataTypeRecord False (doFields fs))
  N.DataType n (N.Node _ (N.PackedRecord fs)) -> (doName n, O.DataTypeRecord True (doFields fs))
  N.DataType n t -> (doName n, O.DataTypeIs (doType t))
  N.Protocol n is -> (doName n, O.ProtocolIs (map doType is))
  N.TaggedProtocol n ts -> (doName n, O.ProtocolCase [(doTag tn, map doType tts) | (N.Node _ (N.Tag tn tts)) <- ts])
  N.Proc n fs p -> (doName n, O.Proc (doFormals fs) (doProcess p))
  N.Func n rs fs vp -> (doName n, O.Function (map doType rs) (doFormals fs) (doValueProcess vp))
  N.FuncIs n rs fs el -> (doName n, O.Function (map doType rs) (doFormals fs) (O.ValOf O.Skip (doExpressionList el)))
  N.Retypes t d s -> (doName d, O.Retypes (doType t) (doVariable s))
  N.ValRetypes t d s -> (doName d, O.ValRetypes (doType t) (doVariable s))
  N.Reshapes t d s -> (doName d, O.Reshapes (doType t) (doVariable s))
  N.ValReshapes t d s -> (doName d, O.ValReshapes (doType t) (doVariable s))

doSpecifications :: N.Node -> (O.Specification -> a -> a) -> a -> a
doSpecifications n@(N.Node m nt) comb arg = case nt of
  N.Vars t [] -> arg
  N.Vars t (v:vs) -> comb (doName v, O.Declaration (doType t)) (doSpecifications (N.Node m (N.Vars t vs)) comb arg)
  otherwise -> comb (doSimpleSpec n) arg

doAlternative :: N.Node -> O.Alternative
doAlternative n@(N.Node _ nt) = case nt of
  N.Guard (N.Node _ (N.In c m)) p -> O.Alternative (doVariable c) (doInputMode m) (doProcess p)
  N.Guard (N.Node _ (N.CondGuard b (N.Node _ (N.In c m)))) p -> O.AlternativeCond (doExpression b) (doVariable c) (doInputMode m) (doProcess p)
  N.Guard (N.Node _ (N.CondGuard b (N.Node _ N.Skip))) p -> O.AlternativeSkip (doExpression b) (doProcess p)
  -- ALT over "? CASE": the O.Skip that gets inserted here doesn't correspond
  -- to anything in real occam; it's just there to let us handle these the same
  -- way as the regular ALT inputs.
  N.In c m@(N.Node _ (N.InCase _)) -> O.Alternative (doVariable c) (doInputMode m) O.Skip
  N.CondGuard b (N.Node _ (N.In c m@(N.Node _ (N.InCase _)))) -> O.AlternativeCond (doExpression b) (doVariable c) (doInputMode m) O.Skip

doAlt :: N.Node -> O.Structured O.Alternative
doAlt n@(N.Node _ nt) = case nt of
  N.Alt ns -> O.Several $ map doAlt ns
  N.PriAlt ns -> O.Several $ map doAlt ns
  N.AltRep r n -> O.Rep (doReplicator r) (doAlt n)
  N.PriAltRep r n -> O.Rep (doReplicator r) (doAlt n)
  N.Decl s n -> doSpecifications s O.Spec (doAlt n)
  otherwise -> O.Only $ doAlternative n

doValueProcess :: N.Node -> O.ValueProcess
doValueProcess n@(N.Node _ nt) = case nt of
  N.Decl s n -> doSpecifications s O.ValOfSpec (doValueProcess n)
  N.ValOf p el -> O.ValOf (doProcess p) (doExpressionList el)

doPlacedPar :: N.Node -> O.Structured O.Process
doPlacedPar n@(N.Node _ nt) = case nt of
  N.PlacedPar ps -> O.Several $ map doPlacedPar ps
  N.PlacedParRep r p -> O.Rep (doReplicator r) (doPlacedPar p)
  N.Processor e p -> O.Only $ O.Processor (doExpression e) (doProcess p)
  N.Decl s p -> doSpecifications s O.Spec (doPlacedPar p)

doProcess :: N.Node -> O.Process
doProcess n@(N.Node _ nt) = case nt of
  N.Decl s p -> doSpecifications s O.ProcSpec (doProcess p)
  N.Assign vs el -> O.Assign (map doVariable vs) (doExpressionList el)
  N.In c m -> O.Input (doVariable c) (doInputMode m)
  N.Out c os -> O.Output (doVariable c) (map doOutputItem os)
  N.OutCase c t os -> O.OutputCase (doVariable c) (doTag t) (map doOutputItem os)
  N.Skip -> O.Skip
  N.Stop -> O.Stop
  N.MainProcess -> O.Main
  N.Seq ps -> O.Seq (map doProcess ps)
  N.SeqRep r p -> O.ReplicatedSeq (doReplicator r) (doProcess p)
  N.If _ -> O.If $ doChoice n
  N.Case e os -> O.Case (doExpression e) (O.Several $ map doOption os)
  N.While e p -> O.While (doExpression e) (doProcess p)
  N.Par ns -> O.Par False (map doProcess ns)
  N.PriPar ns -> O.Par True (map doProcess ns)
  N.ParRep r p -> O.ParRep False (doReplicator r) (doProcess p)
  N.PriParRep r p -> O.ParRep True (doReplicator r) (doProcess p)
  N.PlacedPar _ -> O.PlacedPar $ doPlacedPar n
  N.PlacedParRep _ _ -> O.PlacedPar $ doPlacedPar n
  N.Processor _ _ -> O.PlacedPar $ doPlacedPar n
  N.Alt _ -> O.Alt False $ doAlt n
  N.AltRep _ _ -> O.Alt False $ doAlt n
  N.PriAlt _ -> O.Alt True $ doAlt n
  N.PriAltRep _ _ -> O.Alt True $ doAlt n
  N.ProcCall p es -> O.ProcCall (doName p) (map doExpression es)

ptToAST :: N.Node -> O.Process
ptToAST = doProcess

