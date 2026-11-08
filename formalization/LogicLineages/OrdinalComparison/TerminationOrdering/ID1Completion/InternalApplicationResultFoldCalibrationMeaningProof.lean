module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationMeaningProof
open InternalApplicationResultStack InternalApplicationResultFoldCalibration

theorem actualOriginalSemanticResultFoldEquation :
    InternalApplicationResultFoldCalibrationTargets.ActualOriginalSemanticResultFoldEquation := by
  intro guard leaf combine value
  rw [semanticFold]
  split_ifs <;> rfl

theorem stepMeaning (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat)
    (state : State) :
    stateMeaning guard leaf combine (stateStep guard leaf combine state) =
      stateMeaning guard leaf combine state := by
  rcases state with ⟨s, xs, ys⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => rfl
    | cons frame rest =>
      by_cases ht : (Nat.unpair frame).1 = 0
      · have he := actualOriginalSemanticResultFoldEquation guard leaf combine (Nat.unpair frame).2
        by_cases ho : InternalApplicationValidityStack.tagValue (Nat.unpair frame).2 = 2 ∧
            guard (Nat.unpair frame).2 = 1
        · simp only [ho, if_true] at he
          simp [stateStep, stateMeaning, workMeaning, visitValue, finishValue, ht, ho, he]
        · simp only [ho, if_false] at he
          simp [stateStep, stateMeaning, workMeaning, ht, ho, he]
      · by_cases hf : (Nat.unpair frame).1 = 1
        · cases ys with
          | nil => simp [stateStep, stateMeaning, workMeaning, failedState, ht, hf]
          | cons argument ys =>
            cases ys with
            | nil => simp [stateStep, stateMeaning, workMeaning, failedState, ht, hf]
            | cons function results =>
                simp [stateStep, stateMeaning, workMeaning, ht, hf]
        · simp [stateStep, stateMeaning, workMeaning, failedState, ht, hf]
  · simp [stateStep, stateMeaning, failedState, hs]

theorem iterateMeaning (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat)
    (count : Nat) (state : State) :
    stateMeaning guard leaf combine (stateIterate guard leaf combine count state) =
      stateMeaning guard leaf combine state := by
  induction count with
  | zero => rfl
  | succ count ih => rw [stateIterate, stepMeaning, ih]

theorem actualOriginalResultStackMeaningInvariant :
    InternalApplicationResultFoldCalibrationTargets.ActualOriginalResultStackMeaningInvariant := by
  intro guard leaf combine
  exact ⟨stepMeaning guard leaf combine, iterateMeaning guard leaf combine⟩

theorem terminalResult (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat)
    (state : State) (results : List Nat) (ht : terminal state)
    (hm : stateMeaning guard leaf combine state = some results) :
    state = (⟨1, [], results⟩ : State) := by
  rcases ht with rfl | ⟨hs, hw⟩
  · simp [stateMeaning, failedState] at hm
  · rcases state with ⟨s, xs, ys⟩
    simp only at hs hw
    subst s
    subst xs
    have hy : ys = results := by simpa [stateMeaning, workMeaning] using hm
    subst ys
    rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationMeaningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationMeaningProof
