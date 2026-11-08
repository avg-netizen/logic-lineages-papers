module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationExecutionProof
open InternalApplicationValidityStack InternalApplicationValidityCalibration
open InternalApplicationValidityStackEvaluationProof InternalApplicationValidityStackStateProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem iterateZero (node leaf : Program 1) (value : Nat) :
    evaluate (iterate node leaf) (List.Vector.ofFn ![0, value]) = value := rfl

 theorem iterateSuccessor (node leaf : Program 1) (count value : Nat) :
    evaluate (iterate node leaf) (List.Vector.ofFn ![count + 1, value]) =
      evaluate (transition node leaf) (List.Vector.ofFn ![
        evaluate (iterate node leaf) (List.Vector.ofFn ![count, value])]) := by
  change evaluate (transition node leaf) (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (iterate node leaf) (List.Vector.ofFn ![count, value])) = _
  congr 1

 theorem actualOriginalEncodedStackIteration :
    InternalApplicationValidityCalibrationTargets.ActualOriginalEncodedStackIteration := by
  intro node leaf count state
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [iterateSuccessor, ih, actualOriginalStackTransitionCalibration,
      actualOriginalEncodedStackTransition]
    rfl

 theorem stateIterateStep (node leaf : Nat → Nat) (count : Nat) (state : State) :
    stateIterate node leaf count (stateStep node leaf state) =
      stateStep node leaf (stateIterate node leaf count state) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [stateIterate, ih]

 theorem stateIterateSuccessorFirst (node leaf : Nat → Nat) (count : Nat) (state : State) :
    stateIterate node leaf (count + 1) state =
      stateIterate node leaf count (stateStep node leaf state) := by
  exact (stateIterateStep node leaf count state).symm

 theorem terminalStep (node leaf : Nat → Nat) (state : State) (h : terminal state) :
    stateStep node leaf state = state := by
  rcases h with rfl | rfl <;> simp [stateStep, failedState]

 theorem terminalIterate (node leaf : Nat → Nat) (state : State) (count : Nat)
    (h : terminal state) : stateIterate node leaf count state = state := by
  induction count with
  | zero => rfl
  | succ count ih => rw [stateIterate, ih, terminalStep node leaf state h]

 theorem stepLiveOrFailed (node leaf : Nat → Nat) (state : State) :
    (stateStep node leaf state).status = 1 ∨ stateStep node leaf state = failedState := by
  rcases state with ⟨s, xs⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => exact Or.inl rfl
    | cons value rest =>
      by_cases ht : tagValue value = 2 <;>
        by_cases hn : node (resultTypeValue value) = 1 <;>
        by_cases hl : leaf value = 1 <;>
        simp [stateStep, ht, hn, hl]
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
  | cons value rest => rw [workWeightCons]; omega

 theorem liveSufficientFuel (node leaf : Nat → Nat) (count : Nat) :
    ∀ state : State, state.status = 1 → workWeight state.work ≤ count →
      terminal (stateIterate node leaf count state) := by
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
      rw [terminalIterate node leaf state (count + 1) ht]
      exact ht
    · have hd := actualOriginalStackWorkDecrease node leaf state hs he
      rw [stateIterateSuccessorFirst]
      rcases stepLiveOrFailed node leaf state with hnext | hfailed
      · exact ih _ hnext (by omega)
      · rw [hfailed, terminalIterate node leaf failedState count (Or.inl rfl)]
        exact Or.inl rfl

 theorem arbitrarySufficientFuel (node leaf : Nat → Nat) (state : State) (count : Nat)
    (hw : workWeight state.work + 1 ≤ count) : terminal (stateIterate node leaf count state) := by
  by_cases hs : state.status = 1
  · exact liveSufficientFuel node leaf count state hs (by omega)
  · cases count with
    | zero => omega
    | succ count =>
      rw [stateIterateSuccessorFirst]
      have hf : stateStep node leaf state = failedState := by simp [stateStep, hs]
      rw [hf, terminalIterate node leaf failedState count (Or.inl rfl)]
      exact Or.inl rfl

 theorem actualOriginalStackSufficientFuel :
    InternalApplicationValidityCalibrationTargets.ActualOriginalStackSufficientFuel := by
  intro node leaf state count
  exact ⟨liveSufficientFuel node leaf count state,
    arbitrarySufficientFuel node leaf state count,
    terminalIterate node leaf state count⟩

 theorem fuelEvaluation (v : List.Vector Nat 1) :
    evaluate fuel v = payloadValue (v.get 0) + 1 := by
  change evaluate InternalUnpair.right v + 1 = _
  rw [rightEvaluation]
  rfl

 theorem initialEvaluation (v : List.Vector Nat 1) :
    evaluate initial v = encodeState (⟨1, [v.get 0]⟩ : State) := by
  rw [initial, pairOfEvaluation, oneEvaluation, consOfEvaluation, zeroEvaluation]
  rfl

 theorem runEvaluation (node leaf : Program 1) (v : List.Vector Nat 1) :
    evaluate (run node leaf) v =
      encodeState (stateIterate
        (fun value => evaluate node (List.Vector.ofFn ![value]))
        (fun value => evaluate leaf (List.Vector.ofFn ![value]))
        (payloadValue (v.get 0) + 1) (⟨1, [v.get 0]⟩ : State)) := by
  change evaluate (iterate node leaf)
    (List.Vector.ofFn fun i : Fin 2 => evaluate ((![fuel, initial] : Fin 2 → Program 1) i) v) = _
  have hv : (List.Vector.ofFn fun i : Fin 2 =>
      evaluate ((![fuel, initial] : Fin 2 → Program 1) i) v) =
      List.Vector.ofFn ![payloadValue (v.get 0) + 1, encodeState (⟨1, [v.get 0]⟩ : State)] := by
    apply List.Vector.ext
    intro i
    simp only [List.Vector.get_ofFn]
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
    · exact fuelEvaluation v
    · exact initialEvaluation v
  rw [hv, actualOriginalEncodedStackIteration]

 theorem finishedEvaluation (v : List.Vector Nat 1) :
    evaluate finished v =
      if (Nat.unpair (v.get 0)).1 = 1 ∧ (Nat.unpair (v.get 0)).2 = 0 then 1 else 0 := by
  rw [finished, conjunctionEvaluation, exactOneEvaluation, statusEvaluation,
    sameEvaluation, workEvaluation, zeroEvaluation]
  split_ifs <;> simp_all

 theorem finishedEncodedEvaluation (state : State) :
    evaluate finished (List.Vector.ofFn ![encodeState state]) =
      if state.status = 1 ∧ state.work = [] then 1 else 0 := by
  rw [finishedEvaluation]
  have hc : NumberedMultisetNumeric.numbersNumber state.work = 0 ↔ state.work = [] := by
    cases state.work <;> simp [NumberedMultisetNumeric.numbersNumber]
  simp [encodeState, hc]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationExecutionProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationExecutionProof
