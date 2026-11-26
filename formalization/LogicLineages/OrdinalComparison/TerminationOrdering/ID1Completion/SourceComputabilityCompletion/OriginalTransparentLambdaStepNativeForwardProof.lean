module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeForwardProof
open OriginalHereditaryLambda (childValues matchingTargetValue)
open OriginalHereditaryLambdaRawProof
open InternalOriginalUniformApplicationStepSelection
open InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A literal matching lambda target is never the same-type bottom target,
including when its raw body is malformed. -/
theorem matchingNotBottom (v : List.Vector Nat 4) (hm : matchingTargetValue v = 1) :
    evaluate OriginalLambdaGuardLeaf.sameBottom v ≠ 1 := by
  have htag : (Nat.unpair (Nat.unpair (v.get 1)).2).1 = 1 := by
    unfold matchingTargetValue at hm
    split at hm
    next h => exact h.1
    next => contradiction
  intro hb
  rw [OriginalLambdaGuardLeafEvaluationSupportProof.sameBottomEvaluation] at hb
  split at hb
  next he =>
    rw [he] at htag
    simp only [Nat.unpair_pair] at htag
    contradiction
  next => contradiction

/-- The existing same-certificate lambda inversion pays the forward
acceptance direction. No completeness-selected certificate is substituted. -/
theorem leafChildAccept (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4)
    (hcal : LeafCalibrated n arity oldStep) (v : List.Vector Nat 4)
    (hl : evaluate OriginalLambdaGuardLeaf.sourceLambda v = 1)
    (hm : matchingTargetValue v = 1)
    (ha : leafValue n arity v = 1) :
    leafValue n arity (childValues v) = 1 := by
  have hg := OriginalLambdaGuardLeafEvaluationProof.leafChildAccept n arity oldStep hcal v
    ha hl (matchingNotBottom v hm)
  rw [OriginalLambdaGuardLeaf.childGuard,conjunctionEvaluation] at hg
  have hc : evaluate (OriginalLambdaGuardLeaf.childCheck oldStep) v = 1 := by
    split at hg
    next h => exact h.2
    next => contradiction
  rw [childCheckEvaluation,hcal] at hc
  exact hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeForwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeForwardProof
