module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceNormalizedProof
open InternalOriginalUniformDescentSelection (Data Calibrated)
open OriginalHereditaryValidity

theorem normalizedCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) : Calibrated n arity (normalizedData data) := by
  exact InternalOriginalUniformContextMembershipEvaluationProof.actualOriginalUniformNormalizedMembershipCalibration
    n arity (BottomParameter.baseData data)
    (BottomParameterEvaluationProof.actualOriginalBottomParameterCalibration n arity data hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceNormalizedProof
