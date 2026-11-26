module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSemanticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalDecreaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalEncodedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalExecutionProof
open OriginalLambdaTraversal OriginalLambdaTraversalSemanticProof
open OriginalLambdaTraversalWeightProof OriginalLambdaTraversalDecreaseProof
open OriginalLambdaTraversalEncodedProof

theorem encodedIteration (leaf : Nat → Nat → Nat) (count : Nat) (state : State) :
    iterateValue leaf count (encodeState state) = encodeState (stateIterate leaf count state) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change transitionValue leaf (iterateValue leaf count (encodeState state)) = _
    rw [ih, actualOriginalLambdaTraversalEncodedTransition]
    rfl

theorem stateIterateStep (leaf : Nat → Nat → Nat) (count : Nat) (state : State) :
    stateIterate leaf count (stateStep leaf state) = stateStep leaf (stateIterate leaf count state) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [stateIterate, ih]

theorem stateIterateSuccessorFirst (leaf : Nat → Nat → Nat) (count : Nat) (state : State) :
    stateIterate leaf (count + 1) state = stateIterate leaf count (stateStep leaf state) :=
  (stateIterateStep leaf count state).symm

theorem terminalStep (leaf : Nat → Nat → Nat) (state : State) (h : terminal state) :
    stateStep leaf state = state := by
  rcases h with rfl | ⟨hs, hw⟩
  · simp [stateStep, failedState, InternalApplicationResultStack.failedState]
  · simp [stateStep, hs, hw]

theorem terminalIterate (leaf : Nat → Nat → Nat) (state : State) (count : Nat)
    (h : terminal state) : stateIterate leaf count state = state := by
  induction count with
  | zero => rfl
  | succ count ih => rw [stateIterate, ih, terminalStep leaf state h]

theorem stepLiveOrFailed (leaf : Nat → Nat → Nat) (state : State) :
    (stateStep leaf state).status = 1 ∨ stateStep leaf state = failedState := by
  rcases state with ⟨s, xs, ys⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => exact Or.inl rfl
    | cons frame rest =>
      by_cases ht : (Nat.unpair frame).1 = 0
      · by_cases ha : tagValue (Nat.unpair (Nat.unpair frame).2).1 = 2 <;>
          by_cases hl : tagValue (Nat.unpair (Nat.unpair frame).2).1 = 1 <;>
          simp [stateStep, ht, ha, hl]
      · by_cases ha : (Nat.unpair frame).1 = 1
        · cases ys with
          | nil => simp [stateStep, ht, ha]
          | cons argument ys =>
            cases ys with
            | nil => simp [stateStep, ht, ha]
            | cons function results => simp [stateStep, ht, ha]
        · by_cases hl : (Nat.unpair frame).1 = 2
          · cases ys with
            | nil => simp [stateStep, ht, ha, hl]
            | cons body results => simp [stateStep, ht, ha, hl]
          · simp [stateStep, ht, ha, hl]
  · simp [stateStep, hs]

theorem frameWeightPositive (frame : Nat) : 0 < frameWeight frame := by
  unfold frameWeight
  split_ifs <;> omega

theorem weightPositive (state : State) (hw : state.work ≠ []) : 0 < workWeight state.work := by
  cases hxs : state.work with
  | nil => exact False.elim (hw hxs)
  | cons frame rest =>
    rw [workWeightCons]
    have hp := frameWeightPositive frame
    omega

/-- Work decrease proves terminality, not successful output. The separate
meaning invariant is required to exclude failed or wrong-size result states. -/
theorem liveSufficientFuel (leaf : Nat → Nat → Nat) (count : Nat) :
    ∀ state : State, state.status = 1 → workWeight state.work ≤ count →
      terminal (stateIterate leaf count state) := by
  induction count with
  | zero =>
    intro state hs hw
    by_cases he : state.work = []
    · exact Or.inr ⟨hs, he⟩
    · have hp := weightPositive state he
      omega
  | succ count ih =>
    intro state hs hw
    by_cases he : state.work = []
    · have ht : terminal state := Or.inr ⟨hs, he⟩
      rw [terminalIterate leaf state (count + 1) ht]
      exact ht
    · have hd := actualOriginalLambdaTraversalWorkDecrease leaf state hs he
      rw [stateIterateSuccessorFirst]
      rcases stepLiveOrFailed leaf state with hnext | hfailed
      · exact ih _ hnext (by omega)
      · rw [hfailed, terminalIterate leaf failedState count (Or.inl rfl)]
        exact Or.inl rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalExecutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalExecutionProof
