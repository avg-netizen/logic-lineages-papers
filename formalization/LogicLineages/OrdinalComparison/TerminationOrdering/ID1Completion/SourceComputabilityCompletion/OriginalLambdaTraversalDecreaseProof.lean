module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalWeightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalDecreaseProof
open OriginalLambdaTraversal OriginalLambdaTraversalWeightProof

theorem actualOriginalLambdaTraversalWorkDecrease :
    OriginalLambdaTraversalTargets.ActualOriginalLambdaTraversalWorkDecrease := by
  intro leaf state hs hw
  rcases state with ⟨s, xs, ys⟩
  simp only at hs hw
  subst s
  cases xs with
  | nil => exact False.elim (hw rfl)
  | cons frame rest =>
    by_cases ht : (Nat.unpair frame).1 = 0
    · by_cases ha : tagValue (Nat.unpair (Nat.unpair frame).2).1 = 2
      · have hb := applicationFuelBound (Nat.unpair (Nat.unpair frame).2).1 ha
        simp only [stateStep, ht, ha, if_true, workWeightCons,
          visitWeight, applicationReturnWeight]
        simp only [frameWeight, ht, if_true]
        simp only [fuelValue] at hb
        simp only [fuelValue]
        omega
      · by_cases hl : tagValue (Nat.unpair (Nat.unpair frame).2).1 = 1
        · have hb := lambdaFuelBound (Nat.unpair (Nat.unpair frame).2).1 hl
          have h12 : (1 : Nat) ≠ 2 := by omega
          simp only [stateStep, ht, ha, hl, h12, if_true, if_false, workWeightCons,
            visitWeight, lambdaReturnWeight]
          simp only [frameWeight, ht, if_true]
          simp only [fuelValue] at hb
          rw [fuelValue]
          omega
        · simp only [stateStep, ht, ha, hl, if_true, if_false, workWeightCons,
            frameWeight, ht]
          omega
    · by_cases ha : (Nat.unpair frame).1 = 1
      · cases ys with
        | nil => simp [stateStep, ht, ha, failedState, InternalApplicationResultStack.failedState,
            workWeight, frameWeight]
        | cons a ys =>
          cases ys with
          | nil => simp [stateStep, ht, ha, failedState, InternalApplicationResultStack.failedState,
              workWeight, frameWeight]
          | cons f ys => simp [stateStep, ht, ha, workWeightCons, frameWeight]
      · by_cases hl : (Nat.unpair frame).1 = 2
        · cases ys with
          | nil => simp [stateStep, ht, ha, hl, failedState, InternalApplicationResultStack.failedState,
              workWeight, frameWeight]
          | cons b ys => simp [stateStep, ht, ha, hl, workWeightCons, frameWeight]
        · simp [stateStep, ht, ha, hl, failedState, InternalApplicationResultStack.failedState,
            workWeight, frameWeight]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalDecreaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalDecreaseProof
