module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.NativeLineProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof
open LiteralRawMP.NativeProof (pairEval)
theorem argumentsAt {n : Nat} (f t u : Program n) (v : List.Vector Nat n) (a b c : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate t v = Encodable.encode b)
 (hc : evaluate u v = Encodable.encode c) :
 evaluate (arguments f t u) v = Encodable.encode [a,b,c] := by
 have hcons (x y : Nat) : evaluate HistoryCodec.cons (x ::ᵥ y ::ᵥ nil) = (Nat.pair x y).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 simp only [arguments,twoEval,ha,hb,hc,constantEval,hcons]
 rfl
theorem conclusionAt {n : Nat} (f t u : Program n) (v : List.Vector Nat n) (a b c : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate t v = Encodable.encode b)
 (hc : evaluate u v = Encodable.encode c) :
 evaluate (conclusion f t u) v = Encodable.encode ((GorbowLogicalAxiomCode.case12 0 [a,b,c]).getD []) := by
 rw [conclusion,oneEval,oneEval,argumentsAt f t u v a b c ha hb hc,
  UniformClosedCase12.NativeProof.originalLists]
 cases h : GorbowLogicalAxiomCode.case12 0 [a,b,c] with
 | none =>
  change evaluate HistoryCodec.predecessor (0 ::ᵥ nil) = 0
  rw [HistoryCodec.NativeProof.evaluatePredecessor,Nat.pred_zero]
 | some result =>
  change evaluate HistoryCodec.predecessor ((Encodable.encode result).succ ::ᵥ nil) = Encodable.encode result
  rw [HistoryCodec.NativeProof.evaluatePredecessor,Nat.pred_succ]
theorem lineAt {n : Nat} (f t u : Program n) (v : List.Vector Nat n) (a b c : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate t v = Encodable.encode b)
 (hc : evaluate u v = Encodable.encode c) :
 evaluate (line f t u) v = Encodable.encode (nativeLine a b c) := by
 simp only [line,twoEval,constantEval,conclusionAt f t u v a b c ha hb hc,
  argumentsAt f t u v a b c ha hb hc,pairEval]
 rfl
theorem exactNativeLine : Targets.NativeLine := by
 intro a b c
 exact lineAt (.projection 0) (.projection 1) (.projection 2)
  (Encodable.encode a ::ᵥ Encodable.encode b ::ᵥ Encodable.encode c ::ᵥ nil) a b c rfl rfl rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.NativeLineProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.NativeLineProof
