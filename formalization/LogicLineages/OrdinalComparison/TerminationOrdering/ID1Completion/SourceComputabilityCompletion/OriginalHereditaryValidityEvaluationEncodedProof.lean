module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationEncodedProof
open OriginalHereditaryValidity NumberedMultisetNumeric

theorem actualOriginalHereditaryEncodedTransition :
    OriginalHereditaryValidityTargets.ActualOriginalHereditaryEncodedTransition := by
  intro oldSource oldTarget member state
  have hz : Nat.pair 0 0 = 0 := rfl
  rcases state with ⟨s, xs⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => simp [transitionValue, encodeState, numbersNumber, stateStep]
    | cons frame rest =>
      rcases frame with ⟨value, parameter⟩
      by_cases hc : nodeCheckValue oldSource oldTarget member value parameter = 1 <;>
        by_cases ha : tagValue value = 2 <;>
        by_cases hl : tagValue value = 1 <;>
        simp [transitionValue, encodeState, encodeFrame, numbersNumber, stateStep,
          failedState, hc, ha, hl, Nat.add_comm 1, hz]
  · simp [transitionValue, encodeState, stateStep, failedState, numbersNumber, hs, hz]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationEncodedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationEncodedProof
