module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NativeTickProof
open GorbowPRProgram List.Vector HistoryRuleSuffix.NativeProof
open LiteralRawMP.NativeProof (pairEval)

theorem remainingPair (raw s : Nat) : evaluate remaining (Nat.pair raw s ::ᵥ nil) = raw := by
 rw [remaining,HistoryDecoder.NativeProof.evaluateDecoder,Nat.unpair_pair]
 rfl

theorem statePair (raw s : Nat) : evaluate taskState (Nat.pair raw s ::ᵥ nil) = s := by
 rw [taskState,HistoryDecoder.NativeProof.evaluateDecoder,Nat.unpair_pair]
 rfl

theorem tickEmpty (s : GorbowSyntaxValidation.State) :
 evaluate tick (Nat.pair 0 (Encodable.encode s) ::ᵥ nil) = Nat.pair 0 (Encodable.encode s) := by
 simp only [tick,chooseEval,remainingPair,projectionEval,get2_0,if_pos rfl]
 rfl

theorem tickCons (token : Nat) (raw : List Nat) (s : GorbowSyntaxValidation.State) :
 evaluate tick (Nat.pair (Encodable.encode (token::raw)) (Encodable.encode s) ::ᵥ nil) =
 Nat.pair (Encodable.encode raw) (Encodable.encode (GorbowSyntaxValidation.step s token)) := by
 simp only [tick,chooseEval,remainingPair,twoEval,oneEval,statePair,
   HistoryLookup.NativeProof.tailList,HistoryLookup.NativeProof.headCons]
 have hn : Encodable.encode (token::raw) ≠ 0 := by
   rw [HistoryLookup.NativeProof.encodeCons]; exact Nat.succ_ne_zero _
 rw [if_neg hn,LiteralSyntaxStep.NativeProof.stepAt,pairEval]
 rfl

theorem iteratorZero (s : Nat) : evaluate iterator (0 ::ᵥ s ::ᵥ nil) = s := rfl

theorem iteratorSucc (count s : Nat) : evaluate iterator (count.succ ::ᵥ s ::ᵥ nil) =
 evaluate tick (evaluate iterator (count ::ᵥ s ::ᵥ nil) ::ᵥ nil) := rfl

theorem iteratorFirst (count s : Nat) : evaluate iterator (count.succ ::ᵥ s ::ᵥ nil) =
 evaluate iterator (count ::ᵥ evaluate tick (s ::ᵥ nil) ::ᵥ nil) := by
 induction count generalizing s with
 | zero => rfl
 | succ count ih =>
   rw [iteratorSucc,ih,iteratorSucc]

theorem iteratorRaw (raw : List Nat) (s : GorbowSyntaxValidation.State) :
 evaluate iterator (raw.length ::ᵥ Nat.pair (Encodable.encode raw) (Encodable.encode s) ::ᵥ nil) =
 Nat.pair 0 (Encodable.encode (raw.foldl GorbowSyntaxValidation.step s)) := by
 induction raw generalizing s with
 | nil => rfl
 | cons token raw ih =>
   rw [List.length_cons,iteratorFirst,tickCons,ih]
   rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NativeTickProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NativeTickProof
