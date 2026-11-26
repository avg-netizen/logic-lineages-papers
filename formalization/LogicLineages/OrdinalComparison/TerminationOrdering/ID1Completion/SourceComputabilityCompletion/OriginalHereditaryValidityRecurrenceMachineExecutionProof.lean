module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationEncodedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityWorkProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachineExecutionProof
open OriginalHereditaryValidity OriginalHereditaryValidityRecurrenceMachine
open OriginalHereditaryValidityEvaluationEncodedProof OriginalHereditaryValidityWorkProof

theorem encodedIteration (oldSource oldTarget member : Nat → Nat → Nat)
    (count : Nat) (state : State) :
    iterateValue oldSource oldTarget member count (encodeState state) =
      encodeState (stateIterate oldSource oldTarget member count state) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change transitionValue oldSource oldTarget member
      (iterateValue oldSource oldTarget member count (encodeState state)) =
        encodeState (stateStep oldSource oldTarget member
          (stateIterate oldSource oldTarget member count state))
    rw [ih, actualOriginalHereditaryEncodedTransition]

theorem stateIterateStep (oldSource oldTarget member : Nat → Nat → Nat)
    (count : Nat) (state : State) :
    stateIterate oldSource oldTarget member count (stateStep oldSource oldTarget member state) =
      stateStep oldSource oldTarget member (stateIterate oldSource oldTarget member count state) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [stateIterate, ih]

theorem stateIterateSuccessorFirst (oldSource oldTarget member : Nat → Nat → Nat)
    (count : Nat) (state : State) :
    stateIterate oldSource oldTarget member (count + 1) state =
      stateIterate oldSource oldTarget member count (stateStep oldSource oldTarget member state) :=
  (stateIterateStep oldSource oldTarget member count state).symm

theorem terminalStep (oldSource oldTarget member : Nat → Nat → Nat)
    (state : State) (h : terminal state) :
    stateStep oldSource oldTarget member state = state := by
  rcases h with rfl | rfl <;> simp [stateStep, failedState]

theorem terminalIterate (oldSource oldTarget member : Nat → Nat → Nat)
    (state : State) (count : Nat) (h : terminal state) :
    stateIterate oldSource oldTarget member count state = state := by
  induction count with
  | zero => rfl
  | succ count ih => rw [stateIterate, ih, terminalStep oldSource oldTarget member state h]

theorem stepLiveOrFailed (oldSource oldTarget member : Nat → Nat → Nat) (state : State) :
    (stateStep oldSource oldTarget member state).status = 1 ∨
      stateStep oldSource oldTarget member state = failedState := by
  rcases state with ⟨s, xs⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => exact Or.inl rfl
    | cons frame rest =>
      by_cases hc : nodeCheckValue oldSource oldTarget member frame.raw frame.parameter = 1 <;>
        by_cases ha : tagValue frame.raw = 2 <;>
        by_cases hl : tagValue frame.raw = 1 <;>
        simp [stateStep, hc, ha, hl]
  · simp [stateStep, hs]

theorem liveEmptyTerminal (state : State) (hs : state.status = 1) (hw : state.work = []) :
    terminal state := by
  right
  rcases state with ⟨s, xs⟩
  simp only at hs hw
  subst s
  subst xs
  rfl

theorem weightPositive (state : State) (hw : state.work ≠ []) :
    0 < workWeight state.work := by
  cases hxs : state.work with
  | nil => exact False.elim (hw hxs)
  | cons frame rest => rw [workWeightCons]; omega

/-- The existing strict work decrease pays every visit, including rejection.
Accepted empty and failed states are fixed for all remaining fuel. -/
theorem liveSufficientFuel (oldSource oldTarget member : Nat → Nat → Nat) (count : Nat) :
    ∀ state : State, state.status = 1 → workWeight state.work ≤ count →
      terminal (stateIterate oldSource oldTarget member count state) := by
  induction count with
  | zero =>
    intro state hs hw
    by_cases he : state.work = []
    · exact liveEmptyTerminal state hs he
    · have hp := weightPositive state he
      omega
  | succ count ih =>
    intro state hs hw
    by_cases he : state.work = []
    · have ht := liveEmptyTerminal state hs he
      rw [terminalIterate oldSource oldTarget member state (count + 1) ht]
      exact ht
    · have hd := actualOriginalHereditaryWorkDecrease oldSource oldTarget member state hs he
      rw [stateIterateSuccessorFirst]
      rcases stepLiveOrFailed oldSource oldTarget member state with hnext | hfailed
      · exact ih _ hnext (by omega)
      · rw [hfailed, terminalIterate oldSource oldTarget member failedState count (Or.inl rfl)]
        exact Or.inl rfl

theorem initialEncoded (value parameter : Nat) :
    initialValue value parameter = encodeState (⟨1, [⟨value, parameter⟩]⟩ : State) := rfl

theorem runEncoded (oldSource oldTarget member : Nat → Nat → Nat) (value parameter : Nat) :
    runValue oldSource oldTarget member value parameter =
      encodeState (stateIterate oldSource oldTarget member (payloadValue value + 1)
        (⟨1, [⟨value, parameter⟩]⟩ : State)) := by
  rw [runValue, initialEncoded, encodedIteration]

theorem finishedEncoded (state : State) :
    finishedValue (encodeState state) =
      if state.status = 1 ∧ state.work = [] then 1 else 0 := by
  have hc : NumberedMultisetNumeric.numbersNumber (state.work.map encodeFrame) = 0 ↔
      state.work = [] := by
    cases state.work <;> simp [NumberedMultisetNumeric.numbersNumber]
  simp [finishedValue, encodeState, hc]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachineExecutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachineExecutionProof
