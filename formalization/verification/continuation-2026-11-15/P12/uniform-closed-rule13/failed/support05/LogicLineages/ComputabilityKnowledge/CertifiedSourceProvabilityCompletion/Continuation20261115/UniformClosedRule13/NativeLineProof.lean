module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13.NativeLineProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof
open LiteralRawMP.NativeProof (pairEval)
theorem argumentsAt {n : Nat} (f t : Program n) (v : List.Vector Nat n) (a b : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate t v = Encodable.encode b) :
 evaluate (arguments f t) v = Encodable.encode [a,b] := by
 have hc (x y : Nat) : evaluate HistoryCodec.cons (x ::ᵥ y ::ᵥ nil) = (Nat.pair x y).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 simp only [arguments,twoEval,ha,hb,constantEval,hc]
 rfl
/-- Exact original Option.getD[] codec, including malformed argument rejection. -/
theorem conclusionAt {n : Nat} (f t : Program n) (v : List.Vector Nat n) (a b : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate t v = Encodable.encode b) :
 evaluate (conclusion f t) v = Encodable.encode ((GorbowLogicalAxiomCode.case13 0 [a,b]).getD []) := by
 rw [conclusion,oneEval,oneEval,argumentsAt f t v a b ha hb,
  UniformClosedCase13.StatementChecks.exactOriginalCase13]
 cases h : GorbowLogicalAxiomCode.case13 0 [a,b] with
 | none =>
  change evaluate HistoryCodec.predecessor (0 ::ᵥ nil) = 0
  rw [HistoryCodec.NativeProof.evaluatePredecessor,Nat.pred_zero]
 | some result =>
  change evaluate HistoryCodec.predecessor ((Encodable.encode result).succ ::ᵥ nil) = Encodable.encode result
  rw [HistoryCodec.NativeProof.evaluatePredecessor,Nat.pred_succ]
theorem lineAt {n : Nat} (f t : Program n) (v : List.Vector Nat n) (a b : List Nat)
 (ha : evaluate f v = Encodable.encode a) (hb : evaluate t v = Encodable.encode b) :
 evaluate (line f t) v = Encodable.encode (nativeLine a b) := by
 simp only [line,twoEval,constantEval,conclusionAt f t v a b ha hb,argumentsAt f t v a b ha hb,pairEval]
 rfl
theorem exactNativeLine : Targets.NativeLine := by
 intro a b
 exact lineAt (.projection 0) (.projection 1) (Encodable.encode a ::ᵥ Encodable.encode b ::ᵥ nil) a b rfl rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13.NativeLineProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13.NativeLineProof
