module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityRefinementProof
open OriginalTransparentLambdaValidity
open OriginalTransparentLambdaValidityEqualityProof

theorem actualOriginalTransparentRefinementCalibration :
    OriginalTransparentLambdaValidityTargets.ActualOriginalTransparentRefinementCalibration := by
  intro n arity rawData hc
  have hs := actualOriginalTransparentSourceEquality n arity rawData hc
  have ht := actualOriginalTransparentTargetEquality n arity rawData hc
  refine ⟨rfl,rfl,?_,?_⟩
  · intro v
    exact ⟨hs v,ht v,rfl,rfl⟩
  · refine ⟨?_,?_,hc.2.2.1,hc.2.2.2⟩
    · intro v
      exact (hs v).trans (hc.1 v)
    · intro v
      exact (ht v).trans (hc.2.1 v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityRefinementProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityRefinementProof
