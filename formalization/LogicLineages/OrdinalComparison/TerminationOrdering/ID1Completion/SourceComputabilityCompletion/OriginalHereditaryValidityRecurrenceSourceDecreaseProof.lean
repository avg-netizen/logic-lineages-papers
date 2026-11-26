module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityWorkProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceDecreaseProof
open OriginalHereditaryValidity OriginalHereditaryValidityWorkProof

theorem functionPayloadLess (value : Nat) (h : tagValue value = 2) :
    payloadValue (functionChildValue value) < payloadValue value := by
  have hp := applicationPayloadBound value h
  rw [functionChildPayload]
  omega

theorem argumentPayloadLess (value : Nat) (h : tagValue value = 2) :
    payloadValue (argumentChildValue value) < payloadValue value := by
  have hp := applicationPayloadBound value h
  rw [argumentChildPayload]
  omega

theorem lambdaPayloadLess (value : Nat) (h : tagValue value = 1) :
    payloadValue (lambdaBodyValue value) < payloadValue value := by
  have hp := lambdaPayloadBound value h
  rw [lambdaChildPayload]
  omega

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceDecreaseProof
