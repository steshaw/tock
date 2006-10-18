-- Convert the parse tree into the AST

module PTToAST (ptToAST) where

import Metadata
import qualified PT as N
import qualified AST as O

doName :: N.Node -> O.Name
doName (N.Node m (N.Name s)) = O.Name m s
doName n = error $ "Failed to translate to Name: " ++ (show n)

doTag :: N.Node -> O.Tag
doTag (N.Node m (N.Name s)) = O.Tag m s

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
doSubscript n@(N.Node m nt) = case nt of
  N.SubPlain e -> O.Subscript m (doExpression e)
  N.SubFromFor e f -> O.SubFromFor m (doExpression e) (doExpression f)
  N.SubFrom e -> O.SubFrom m (doExpression e)
  N.SubFor f -> O.SubFor m (doExpression f)

doLiteral :: N.Node -> O.Literal
doLiteral n@(N.Node m nt) = case nt of
  N.TypedLit t l -> O.Literal m (doType t) rep where (O.Literal _ _ rep) = doLiteral l
  N.LitReal s -> O.Literal m O.Real32 (O.RealLiteral m s)
  N.LitInt s -> O.Literal m O.Int (O.IntLiteral m s)
  N.LitHex s -> O.Literal m O.Int (O.HexLiteral m s)
  N.LitByte s -> O.Literal m O.Byte (O.ByteLiteral m s)
  N.LitString s -> O.Literal m (O.ArrayUnsized O.Byte) (O.StringLiteral m s)
  N.LitArray ns -> O.Literal m O.Infer (O.ArrayLiteral m (map doExpression ns))
  N.Sub s l -> O.SubscriptedLiteral m (doSubscript s) (doLiteral l)

doVariable :: N.Node -> O.Variable
doVariable n@(N.Node m nt) = case nt of
  N.Name _ -> O.Variable m (doName n)
  N.Sub s v -> O.SubscriptedVariable m (doSubscript s) (doVariable v)
  _ -> error $ "Failed to translate to Variable: " ++ (show n)

doExpression :: N.Node -> O.Expression
doExpression n@(N.Node m nt) = case nt of
  N.MonadicOp o a -> O.Monadic m (doMonadicOp o) (doExpression a)
  N.DyadicOp o a b -> O.Dyadic m (doDyadicOp o) (doExpression a) (doExpression b)
  N.MostPos t -> O.MostPos m (doType t)
  N.MostNeg t -> O.MostNeg m (doType t)
  N.Size t -> O.Size m (doType t)
  N.Conv t e -> O.Conversion m O.DefaultConversion (doType t) (doExpression e)
  N.Round t e -> O.Conversion m O.Round (doType t) (doExpression e)
  N.Trunc t e -> O.Conversion m O.Trunc (doType t) (doExpression e)
  N.TypedLit _ _ -> O.ExprLiteral m $ doLiteral n
  N.LitReal _ -> O.ExprLiteral m $ doLiteral n
  N.LitInt _ -> O.ExprLiteral m $ doLiteral n
  N.LitHex _ -> O.ExprLiteral m $ doLiteral n
  N.LitByte _ -> O.ExprLiteral m $ doLiteral n
  N.LitString _ -> O.ExprLiteral m $ doLiteral n
  N.LitArray _ -> O.ExprLiteral m $ doLiteral n
  N.True -> O.True m
  N.False -> O.False m
  N.Call f es -> O.FunctionCall m (doName f) (map doExpression es)
  N.BytesIn t -> O.BytesInType m (doType t)
  N.OffsetOf t g -> O.OffsetOf m (doType t) (doTag g)
  otherwise -> O.ExprVariable m (doVariable n)

doExpressionList :: N.Node -> O.ExpressionList
doExpressionList n@(N.Node m nt) = case nt of
  N.Call f es -> O.FunctionCallList m (doName f) (map doExpression es)
  N.ExpList es -> O.ExpressionList m (map doExpression es)

doReplicator :: N.Node -> O.Replicator
doReplicator n@(N.Node m nt) = case nt of
  N.For v f t -> O.For m (doName v) (doExpression f) (doExpression t)

doFields :: [N.Node] -> [(O.Type, O.Tag)]
doFields ns = concat $ [[(doType t, doTag f) | f <- fs] | (N.Node _ (N.Fields t fs)) <- ns]

doFormals :: [N.Node] -> [(O.Type, O.Name)]
doFormals fs = concat $ [[(doType t, doName n) | n <- ns] | (N.Node _ (N.Formals t ns)) <- fs]

doVariant :: N.Node -> O.Structured
doVariant n@(N.Node m nt) = case nt of
  N.Variant (N.Node _ (N.Tag t is)) p -> O.OnlyV m $ O.Variant m (doTag t) (map doInputItem is) (doProcess p)
  N.Decl s v -> doSpecifications s O.Spec (doVariant v)

doChoice :: N.Node -> O.Structured
doChoice n@(N.Node m nt) = case nt of
  N.If cs -> O.Several m $ map doChoice cs
  N.IfRep r c -> O.Rep m (doReplicator r) (doChoice c)
  N.Choice b p -> O.OnlyC m $ O.Choice m (doExpression b) (doProcess p)
  N.Decl s c -> doSpecifications s O.Spec (doChoice c)

doOption :: N.Node -> O.Structured
doOption n@(N.Node m nt) = case nt of
  N.CaseExps cs p -> O.OnlyO m $ O.Option m (map doExpression cs) (doProcess p)
  N.Else p -> O.OnlyO m $ O.Else m (doProcess p)
  N.Decl s o -> doSpecifications s O.Spec (doOption o)

doInputItem :: N.Node -> O.InputItem
doInputItem n@(N.Node m nt) = case nt of
  N.Counted c d -> O.InCounted m (doVariable c) (doVariable d)
  otherwise -> O.InVariable m (doVariable n)

doOutputItem :: N.Node -> O.OutputItem
doOutputItem n@(N.Node m nt) = case nt of
  N.Counted c d -> O.OutCounted m (doExpression c) (doExpression d)
  otherwise -> O.OutExpression m (doExpression n)

doInputMode :: N.Node -> O.InputMode
doInputMode n@(N.Node m nt) = case nt of
  N.InSimple is -> O.InputSimple m (map doInputItem is)
  N.InCase vs -> O.InputCase m (O.Several m $ map doVariant vs)
  N.InTag (N.Node _ (N.Tag t is)) -> O.InputCase m (O.OnlyV m $ O.Variant m (doTag t) (map doInputItem is) (O.Skip m))
  N.InAfter e -> O.InputAfter m (doExpression e)

doSimpleSpec :: N.Node -> O.Specification
doSimpleSpec n@(N.Node m nt) = case nt of
  N.Is d v -> (doName d, O.Is m O.Infer (doVariable v))
  N.IsType t d v -> (doName d, O.Is m (doType t) (doVariable v))
  N.ValIs d e -> (doName d, O.ValIs m O.Infer (doExpression e))
  N.ValIsType t d e -> (doName d, O.ValIs m (doType t) (doExpression e))
  N.Place v e -> (doName v, O.Place m (doExpression e))
  N.DataType n (N.Node _ (N.Record fs)) -> (doName n, O.DataTypeRecord m False (doFields fs))
  N.DataType n (N.Node _ (N.PackedRecord fs)) -> (doName n, O.DataTypeRecord m True (doFields fs))
  N.DataType n t -> (doName n, O.DataTypeIs m (doType t))
  N.Protocol n is -> (doName n, O.ProtocolIs m (map doType is))
  N.TaggedProtocol n ts -> (doName n, O.ProtocolCase m [(doTag tn, map doType tts) | (N.Node _ (N.Tag tn tts)) <- ts])
  N.Proc n fs p -> (doName n, O.Proc m (doFormals fs) (doProcess p))
  N.Func n rs fs vp -> (doName n, O.Function m (map doType rs) (doFormals fs) (doValueProcess vp))
  N.FuncIs n rs fs el -> (doName n, O.Function m (map doType rs) (doFormals fs) (O.ValOf m (O.Skip m) (doExpressionList el)))
  N.Retypes t d s -> (doName d, O.Retypes m (doType t) (doVariable s))
  N.ValRetypes t d s -> (doName d, O.ValRetypes m (doType t) (doVariable s))
  N.Reshapes t d s -> (doName d, O.Reshapes m (doType t) (doVariable s))
  N.ValReshapes t d s -> (doName d, O.ValReshapes m (doType t) (doVariable s))

doSpecifications :: N.Node -> (Meta -> O.Specification -> a -> a) -> a -> a
doSpecifications n@(N.Node m nt) comb arg = case nt of
  N.Vars t [] -> arg
  N.Vars t (v:vs) -> comb m (doName v, O.Declaration m (doType t)) (doSpecifications (N.Node m (N.Vars t vs)) comb arg)
  otherwise -> comb m (doSimpleSpec n) arg

doAlternative :: N.Node -> O.Alternative
doAlternative n@(N.Node m nt) = case nt of
  N.Guard (N.Node _ (N.In c md)) p -> O.Alternative m (doVariable c) (doInputMode md) (doProcess p)
  N.Guard (N.Node _ (N.CondGuard b (N.Node _ (N.In c md)))) p -> O.AlternativeCond m (doExpression b) (doVariable c) (doInputMode md) (doProcess p)
  N.Guard (N.Node _ (N.CondGuard b (N.Node _ N.Skip))) p -> O.AlternativeSkip m (doExpression b) (doProcess p)
  -- ALT over "? CASE": the O.Skip that gets inserted here doesn't correspond
  -- to anything in real occam; it's just there to let us handle these the same
  -- way as the regular ALT inputs.
  N.In c md@(N.Node _ (N.InCase _)) -> O.Alternative m (doVariable c) (doInputMode md) (O.Skip m)
  N.CondGuard b (N.Node _ (N.In c md@(N.Node _ (N.InCase _)))) -> O.AlternativeCond m (doExpression b) (doVariable c) (doInputMode md) (O.Skip m)

doAlt :: N.Node -> O.Structured
doAlt n@(N.Node m nt) = case nt of
  N.Alt ns -> O.Several m $ map doAlt ns
  N.PriAlt ns -> O.Several m $ map doAlt ns
  N.AltRep r n -> O.Rep m (doReplicator r) (doAlt n)
  N.PriAltRep r n -> O.Rep m (doReplicator r) (doAlt n)
  N.Decl s n -> doSpecifications s O.Spec (doAlt n)
  otherwise -> O.OnlyA m $ doAlternative n

doValueProcess :: N.Node -> O.ValueProcess
doValueProcess n@(N.Node m nt) = case nt of
  N.Decl s n -> doSpecifications s O.ValOfSpec (doValueProcess n)
  N.ValOf p el -> O.ValOf m (doProcess p) (doExpressionList el)

doPlacedPar :: N.Node -> O.Structured
doPlacedPar n@(N.Node m nt) = case nt of
  N.PlacedPar ps -> O.Several m $ map doPlacedPar ps
  N.PlacedParRep r p -> O.Rep m (doReplicator r) (doPlacedPar p)
  N.Processor e p -> O.OnlyP m $ O.Processor m (doExpression e) (doProcess p)
  N.Decl s p -> doSpecifications s O.Spec (doPlacedPar p)

doProcess :: N.Node -> O.Process
doProcess n@(N.Node m nt) = case nt of
  N.Decl s p -> doSpecifications s O.ProcSpec (doProcess p)
  N.Assign vs el -> O.Assign m (map doVariable vs) (doExpressionList el)
  N.In c md -> O.Input m (doVariable c) (doInputMode md)
  N.Out c os -> O.Output m (doVariable c) (map doOutputItem os)
  N.OutCase c t os -> O.OutputCase m (doVariable c) (doTag t) (map doOutputItem os)
  N.Skip -> O.Skip m
  N.Stop -> O.Stop m
  N.MainProcess -> O.Main m
  N.Seq ps -> O.Seq m (map doProcess ps)
  N.SeqRep r p -> O.SeqRep m (doReplicator r) (doProcess p)
  N.If _ -> O.If m $ doChoice n
  N.Case e os -> O.Case m (doExpression e) (O.Several m $ map doOption os)
  N.While e p -> O.While m (doExpression e) (doProcess p)
  N.Par ns -> O.Par m False (map doProcess ns)
  N.PriPar ns -> O.Par m True (map doProcess ns)
  N.ParRep r p -> O.ParRep m False (doReplicator r) (doProcess p)
  N.PriParRep r p -> O.ParRep m True (doReplicator r) (doProcess p)
  N.PlacedPar _ -> O.PlacedPar m $ doPlacedPar n
  N.PlacedParRep _ _ -> O.PlacedPar m $ doPlacedPar n
  N.Processor _ _ -> O.PlacedPar m $ doPlacedPar n
  N.Alt _ -> O.Alt m False $ doAlt n
  N.AltRep _ _ -> O.Alt m False $ doAlt n
  N.PriAlt _ -> O.Alt m True $ doAlt n
  N.PriAltRep _ _ -> O.Alt m True $ doAlt n
  N.ProcCall p es -> O.ProcCall m (doName p) (map doExpression es)

ptToAST :: N.Node -> O.Process
ptToAST = doProcess

