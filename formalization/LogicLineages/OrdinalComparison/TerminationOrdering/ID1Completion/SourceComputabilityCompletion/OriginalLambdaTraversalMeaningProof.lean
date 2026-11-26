module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSemanticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalMeaningProof
open OriginalLambdaTraversal OriginalLambdaTraversalSemanticProof

/-- One actual transition preserves the complete semantic result list,
including malformed/failed states. No output bound or typedness is used. -/
theorem stepMeaning (leaf : Nat → Nat → Nat) (state : State) :
    stateMeaning leaf (stateStep leaf state) = stateMeaning leaf state := by
  rcases state with ⟨s, xs, ys⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => rfl
    | cons frame rest =>
      by_cases ht : (Nat.unpair frame).1 = 0
      · have he := semanticEquation leaf (Nat.unpair (Nat.unpair frame).2).1
          (Nat.unpair (Nat.unpair frame).2).2
        by_cases ha : tagValue (Nat.unpair (Nat.unpair frame).2).1 = 2
        · simp only [ha, if_true] at he
          simp [stateStep, stateMeaning, workMeaning, visitValue, applicationReturnValue, ht, ha, he]
        · by_cases hl : tagValue (Nat.unpair (Nat.unpair frame).2).1 = 1
          · simp only [ha, hl, if_false, if_true] at he
            simp [stateStep, stateMeaning, workMeaning, visitValue, lambdaReturnValue, ht, ha, hl, he]
          · simp only [ha, hl, if_false] at he
            simp [stateStep, stateMeaning, workMeaning, ht, ha, hl, he]
      · by_cases ha : (Nat.unpair frame).1 = 1
        · cases ys with
          | nil => simp [stateStep, stateMeaning, workMeaning, failedState,
              InternalApplicationResultStack.failedState, ht, ha]
          | cons argument ys =>
            cases ys with
            | nil => simp [stateStep, stateMeaning, workMeaning, failedState,
                InternalApplicationResultStack.failedState, ht, ha]
            | cons function results => simp [stateStep, stateMeaning, workMeaning, ht, ha]
        · by_cases hl : (Nat.unpair frame).1 = 2
          · cases ys with
            | nil => simp [stateStep, stateMeaning, workMeaning, failedState,
                InternalApplicationResultStack.failedState, ht, ha, hl]
            | cons body results => simp [stateStep, stateMeaning, workMeaning, ht, ha, hl]
          · simp [stateStep, stateMeaning, workMeaning, failedState,
              InternalApplicationResultStack.failedState, ht, ha, hl]
  · simp [stateStep, stateMeaning, failedState, InternalApplicationResultStack.failedState, hs]

theorem iterateMeaning (leaf : Nat → Nat → Nat) (count : Nat) (state : State) :
    stateMeaning leaf (stateIterate leaf count state) = stateMeaning leaf state := by
  induction count with
  | zero => rfl
  | succ count ih => rw [stateIterate, stepMeaning, ih]

theorem terminalResult (leaf : Nat → Nat → Nat) (state : State) (results : List Nat)
    (ht : terminal state) (hm : stateMeaning leaf state = some results) :
    state = (⟨1, [], results⟩ : State) := by
  rcases ht with rfl | ⟨hs, hw⟩
  · simp [stateMeaning, failedState, InternalApplicationResultStack.failedState] at hm
  · rcases state with ⟨s, xs, ys⟩
    simp only at hs hw
    subst s
    subst xs
    have hy : ys = results := by simpa [stateMeaning, workMeaning] using hm
    subst ys
    rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalMeaningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalMeaningProof
