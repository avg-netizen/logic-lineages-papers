module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceGuardProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceRefinementProof
open OriginalHereditaryValidity
open OriginalHereditaryValidityRecurrenceSourceRootProof
open OriginalHereditaryValidityRecurrenceSourceGuardProof
open InternalApplicationStepPeelEvaluationSupportProof
open InternalOriginalUniformDescentSelection (Data Calibrated)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem refinementOutput (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (v : List.Vector Nat 2) :
    evaluate (refineData data).oldSource v = evaluate data.oldSource v := by
  change evaluate (InternalAcceptance.conjunction data.oldSource (guard data)) v = _
  rw [conjunctionEvaluation,actualOriginalHereditarySourceGuardRedundancy n arity data hc v,hc.1]
  rcases sourceBoolean n arity v with h | h <;> simp [h]

theorem actualOriginalHereditarySourceRefinementCalibration :
    OriginalHereditaryValidityRecurrenceTargets.ActualOriginalHereditarySourceRefinementCalibration := by
  intro n arity data hc
  refine ⟨refinementOutput n arity data hc,?_,hc.2.1,hc.2.2.1,hc.2.2.2⟩
  intro v
  exact (refinementOutput n arity data hc v).trans (hc.1 v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceRefinementProof
