module
public import LogicLineages.StandardControlCurrent.ClosedEvaluationTargets
public import LogicLineages.OrdinalComparison.EncodedCollapseProof
public import LogicLineages.OrdinalComparison.HeadEndpointProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.ClosedEvaluationStatementChecks
open OrdinalComparison

private theorem iterate_lower (t k : Nat) : t + k ≤ (Phi^[k]) t := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h := self_lt_Phi ((Phi^[k]) t)
      omega

theorem program : ClosedEvaluationTargets.FullEncodedClosedEvaluation :=
  fullEncodedClosedEvaluation

theorem pathOrbit : ClosedEvaluationTargets.ActualPathOrbit := by
  intro a ha
  have hf := actualTerminalFirstFinite a ha
  have hi := actualTerminalValueIdentities a ha
  refine ⟨hf.1, hf.2, hi.2, hi.1, ?_⟩
  intro hn
  have hc := congrArg (fun p : Nat × Nat => p.2) ((actualTerminalRecursion a ha).2 hn)
  have hpos : 0 < actualReplacementCount a := by
    change actualReplacementCount a = actualReplacementCount (actualDescentStep a) + 1 at hc
    omega
  have hnorm := actualNonfiniteNormLowerBound a ha hn
  have hbound := iterate_lower (actualOrdinalNorm a) (actualReplacementCount a)
  rw [← hi.2] at hbound
  exact ⟨hpos, by omega⟩

theorem full : ClosedEvaluationTargets.FullClosedEvaluation := ⟨program, pathOrbit⟩

#print axioms program
#print axioms pathOrbit
#print axioms full

end LogicLineages.StandardControlCurrent.ClosedEvaluationStatementChecks
