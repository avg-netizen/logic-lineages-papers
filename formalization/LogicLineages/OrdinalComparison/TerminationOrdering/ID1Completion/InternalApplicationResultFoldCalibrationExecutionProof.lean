module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationExecutionProof
open InternalApplicationResultStack InternalApplicationResultFoldCalibration
open InternalApplicationResultStackEvaluationProof InternalApplicationResultStackStateProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem iterateZero (guard leaf : Program 1) (combine : Program 4) (value : Nat) :
    evaluate (iterate guard leaf combine) (List.Vector.ofFn ![0, value]) = value := rfl

theorem iterateSuccessor (guard leaf : Program 1) (combine : Program 4) (count value : Nat) :
    evaluate (iterate guard leaf combine) (List.Vector.ofFn ![count + 1, value]) =
      evaluate (transition guard leaf combine) (List.Vector.ofFn ![
        evaluate (iterate guard leaf combine) (List.Vector.ofFn ![count, value])]) := by
  change evaluate (transition guard leaf combine) (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (iterate guard leaf combine) (List.Vector.ofFn ![count, value])) = _
  congr 1

theorem actualOriginalEncodedResultStackIteration :
    InternalApplicationResultFoldCalibrationTargets.ActualOriginalEncodedResultStackIteration := by
  intro guard leaf combine count state
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [iterateSuccessor, ih, actualOriginalResultStackTransitionCalibration,
      actualOriginalEncodedResultStackTransition]
    rfl

theorem stateIterateStep (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat)
    (count : Nat) (state : State) :
    stateIterate guard leaf combine count (stateStep guard leaf combine state) =
      stateStep guard leaf combine (stateIterate guard leaf combine count state) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [stateIterate, ih]

theorem stateIterateSuccessorFirst (guard leaf : Nat → Nat)
    (combine : Nat → Nat → Nat → Nat → Nat) (count : Nat) (state : State) :
    stateIterate guard leaf combine (count + 1) state =
      stateIterate guard leaf combine count (stateStep guard leaf combine state) :=
  (stateIterateStep guard leaf combine count state).symm

theorem terminalStep (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat)
    (state : State) (h : terminal state) : stateStep guard leaf combine state = state := by
  rcases h with rfl | ⟨hs, hw⟩
  · simp [stateStep, failedState]
  · simp [stateStep, hs, hw]

theorem terminalIterate (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat)
    (state : State) (count : Nat) (h : terminal state) :
    stateIterate guard leaf combine count state = state := by
  induction count with
  | zero => rfl
  | succ count ih => rw [stateIterate, ih, terminalStep guard leaf combine state h]

theorem stepLiveOrFailed (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat)
    (state : State) :
    (stateStep guard leaf combine state).status = 1 ∨
      stateStep guard leaf combine state = failedState := by
  rcases state with ⟨s, xs, ys⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => exact Or.inl rfl
    | cons frame rest =>
      by_cases ht : (Nat.unpair frame).1 = 0
      · by_cases ho : InternalApplicationValidityStack.tagValue (Nat.unpair frame).2 = 2 ∧
            guard (Nat.unpair frame).2 = 1 <;>
          simp [stateStep, ht, ho]
      · by_cases hf : (Nat.unpair frame).1 = 1
        · cases ys with
          | nil => simp [stateStep, ht, hf]
          | cons argument ys =>
            cases ys with
            | nil => simp [stateStep, ht, hf]
            | cons function results => simp [stateStep, ht, hf]
        · simp [stateStep, ht, hf]
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

theorem liveSufficientFuel (guard leaf : Nat → Nat)
    (combine : Nat → Nat → Nat → Nat → Nat) (count : Nat) :
    ∀ state : State, state.status = 1 → workWeight state.work ≤ count →
      terminal (stateIterate guard leaf combine count state) := by
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
      rw [terminalIterate guard leaf combine state (count + 1) ht]
      exact ht
    · have hd := actualOriginalResultStackWorkDecrease guard leaf combine state hs he
      rw [stateIterateSuccessorFirst]
      rcases stepLiveOrFailed guard leaf combine state with hnext | hfailed
      · exact ih _ hnext (by omega)
      · rw [hfailed, terminalIterate guard leaf combine failedState count (Or.inl rfl)]
        exact Or.inl rfl

theorem arbitrarySufficientFuel (guard leaf : Nat → Nat)
    (combine : Nat → Nat → Nat → Nat → Nat) (state : State) (count : Nat)
    (hw : workWeight state.work + 1 ≤ count) :
    terminal (stateIterate guard leaf combine count state) := by
  by_cases hs : state.status = 1
  · exact liveSufficientFuel guard leaf combine count state hs (by omega)
  · cases count with
    | zero => omega
    | succ count =>
      rw [stateIterateSuccessorFirst]
      have hf : stateStep guard leaf combine state = failedState := by simp [stateStep, hs]
      rw [hf, terminalIterate guard leaf combine failedState count (Or.inl rfl)]
      exact Or.inl rfl

theorem actualOriginalResultStackSufficientFuel :
    InternalApplicationResultFoldCalibrationTargets.ActualOriginalResultStackSufficientFuel := by
  intro guard leaf combine state count
  exact ⟨liveSufficientFuel guard leaf combine count state,
    arbitrarySufficientFuel guard leaf combine state count,
    terminalIterate guard leaf combine state count⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationExecutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationExecutionProof
