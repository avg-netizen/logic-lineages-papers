module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachineInvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachineExecutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceNumericProof
open OriginalHereditaryValidity OriginalHereditaryValidityRecurrenceMachine
open OriginalHereditaryValidityRecurrenceMachineInvariantProof
open OriginalHereditaryValidityRecurrenceMachineExecutionProof

/-- The actual payload+1 execution is equivalent to the explicit native
acceptance tree. Sufficient fuel is proved for this literal singleton frame;
no run-success, recurrence or termination hypothesis is supplied. -/
theorem validatorNativeAcceptance (oldSource oldTarget member : Nat → Nat → Nat)
    (value parameter : Nat) :
    validatorValue oldSource oldTarget member value parameter = 1 ↔
      NativeAccepted oldSource oldTarget member value parameter := by
  rw [validatorValue, runEncoded, finishedEncoded]
  have ht := liveSufficientFuel oldSource oldTarget member (payloadValue value + 1)
    (⟨1, [⟨value, parameter⟩]⟩ : State) rfl (by simp [workWeight])
  have he := (terminalAcceptance oldSource oldTarget member _ ht).trans
    (iterateInvariant oldSource oldTarget member (payloadValue value + 1)
      (⟨1, [⟨value, parameter⟩]⟩ : State))
  have hc :
      ((stateIterate oldSource oldTarget member (payloadValue value + 1)
          (⟨1, [⟨value, parameter⟩]⟩ : State)).status = 1 ∧
        (stateIterate oldSource oldTarget member (payloadValue value + 1)
          (⟨1, [⟨value, parameter⟩]⟩ : State)).work = []) ↔
      NativeAccepted oldSource oldTarget member value parameter := by
    simpa [stateAccepted] using he
  simpa using hc

/-- The frozen SAME-validator recurrence, including every raw rejected input.
Each child is connected back to its own actual payload+1 machine run. -/
theorem actualOriginalHereditaryValidatorRecurrence :
    OriginalHereditaryValidityRecurrenceTargets.ActualOriginalHereditaryValidatorRecurrence := by
  intro oldSource oldTarget member value parameter
  constructor
  · unfold validatorValue finishedValue
    split_ifs <;> simp
  · simpa only [← validatorNativeAcceptance] using
      nativeAcceptanceEquation oldSource oldTarget member value parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceNumericProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceNumericProof
