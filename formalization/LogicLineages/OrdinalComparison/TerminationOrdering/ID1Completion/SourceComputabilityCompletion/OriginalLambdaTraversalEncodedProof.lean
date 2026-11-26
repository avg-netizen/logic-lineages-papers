module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalEncodedProof
open OriginalLambdaTraversal NumberedMultisetNumeric

/-- The proof splits every raw frame tag and every result-stack underflow,
not merely well-formed frames produced by an initialized run. -/
theorem actualOriginalLambdaTraversalEncodedTransition :
    OriginalLambdaTraversalTargets.ActualOriginalLambdaTraversalEncodedTransition := by
  intro leaf state
  have hz : Nat.pair 0 0 = 0 := rfl
  rcases state with ⟨s, xs, ys⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => simp [transitionValue, encodeState, InternalApplicationResultStack.encodeState,
        numbersNumber, stateStep]
    | cons frame rest =>
      by_cases ht : (Nat.unpair frame).1 = 0
      · by_cases ha : tagValue (Nat.unpair (Nat.unpair frame).2).1 = 2 <;>
          by_cases hl : tagValue (Nat.unpair (Nat.unpair frame).2).1 = 1 <;>
          simp [transitionValue, encodeState, InternalApplicationResultStack.encodeState,
            numbersNumber, stateStep, ht, ha, hl, Nat.add_comm 1]
      · by_cases ha : (Nat.unpair frame).1 = 1
        · cases ys with
          | nil => simp [transitionValue, encodeState, InternalApplicationResultStack.encodeState,
              numbersNumber, stateStep, ht, ha, failedState, InternalApplicationResultStack.failedState, hz]
          | cons a ys =>
            cases ys with
            | nil => simp [transitionValue, encodeState, InternalApplicationResultStack.encodeState,
                numbersNumber, stateStep, ht, ha, failedState, InternalApplicationResultStack.failedState,
                hz, Nat.add_comm 1]
            | cons f ys => simp [transitionValue, encodeState, InternalApplicationResultStack.encodeState,
                numbersNumber, stateStep, ht, ha, Nat.add_comm 1]
        · by_cases hl : (Nat.unpair frame).1 = 2
          · cases ys with
            | nil => simp [transitionValue, encodeState, InternalApplicationResultStack.encodeState,
                numbersNumber, stateStep, ht, ha, hl, failedState, InternalApplicationResultStack.failedState, hz]
            | cons b ys => simp [transitionValue, encodeState, InternalApplicationResultStack.encodeState,
                numbersNumber, stateStep, ht, ha, hl, Nat.add_comm 1]
          · simp [transitionValue, encodeState, InternalApplicationResultStack.encodeState,
              numbersNumber, stateStep, ht, ha, hl, failedState, InternalApplicationResultStack.failedState,
              hz, Nat.add_comm 1]
  · simp [transitionValue, encodeState, InternalApplicationResultStack.encodeState,
      numbersNumber, stateStep, hs, failedState, InternalApplicationResultStack.failedState, hz]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalEncodedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalEncodedProof
