module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportWeightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDecreaseProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportWeightProof

 theorem actualRawSyntaxWorkDecrease : OriginalRawSyntaxTransportTargets.ActualRawSyntaxWorkDecrease := by
  intro mode state hs hw
  have h21 : (2 : Nat) ≠ 1 := by omega
  rcases state with ⟨s, xs, ys⟩
  simp only at hs hw
  subst s
  cases xs with
  | nil => exact False.elim (hw rfl)
  | cons frame rest =>
    by_cases ht : (Nat.unpair frame).1 = 0
    · by_cases h1 : arityValue (Nat.unpair (Nat.unpair (Nat.unpair frame).2).2).2 = 1
      · have hb := unaryFuelBound (Nat.unpair (Nat.unpair (Nat.unpair frame).2).2).2 h1
        simp only [stateStep, ht, h1, if_true, workWeightCons, visitWeight, finishWeight]
        simp only [frameWeight, ht, if_true]
        simp only [fuelValue] at hb
        simp only [fuelValue]
        omega
      · by_cases h2 : arityValue (Nat.unpair (Nat.unpair (Nat.unpair frame).2).2).2 = 2
        · have hb := binaryFuelBound (Nat.unpair (Nat.unpair (Nat.unpair frame).2).2).2 h2
          simp only [stateStep, ht, h1, h2, h21, if_true, if_false,
            workWeightCons, visitWeight, finishWeight]
          simp only [frameWeight, ht, if_true]
          simp only [fuelValue] at hb
          simp only [fuelValue]
          omega
        · simp only [stateStep, ht, h1, h2, h21, if_true, if_false,
            workWeightCons, frameWeight, ht]
          omega
    · by_cases hf : (Nat.unpair frame).1 = 1
      · by_cases h1 : arityValue (Nat.unpair frame).2 = 1
        · cases ys <;> simp [stateStep, ht, hf, h1, failedState,
            InternalApplicationResultStack.failedState, workWeight, frameWeight]
        · by_cases h2 : arityValue (Nat.unpair frame).2 = 2
          · cases ys with
            | nil => simp [stateStep, ht, hf, h1, h2, failedState,
                InternalApplicationResultStack.failedState, workWeight, frameWeight]
            | cons second ys =>
              cases ys <;> simp [stateStep, ht, hf, h1, h2, failedState,
                InternalApplicationResultStack.failedState, workWeight, frameWeight]
          · simp [stateStep, ht, hf, h1, h2, failedState,
              InternalApplicationResultStack.failedState, workWeight, frameWeight]
      · simp [stateStep, ht, hf, failedState,
          InternalApplicationResultStack.failedState, workWeight, frameWeight]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDecreaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDecreaseProof
