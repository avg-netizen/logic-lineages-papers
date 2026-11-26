module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericStepProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalLessThan (ltTest)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
open NumberedWindowInternalSparsePathAdvanceTargets (encodeState)
open NumberedWindowInternalSparseOrderedMinimum

theorem unaryValue {n : Nat} (outer : Program 1) (inner : Program n) (xs : List.Vector Nat n) :
    evaluate (.composition outer (fun _ : Fin 1 => inner)) xs =
      evaluate outer (evaluate inner xs ::ᵥ nil) := by
  change evaluate outer (List.Vector.ofFn (fun _ : Fin 1 => evaluate inner xs)) = _
  rw [vectorOne]

private abbrev tape (h prior : Nat) : List.Vector Nat 2 := h ::ᵥ prior ::ᵥ nil

private theorem priorValue (h prior : Nat) :
    evaluate (.projection (1 : Fin 2)) (tape h prior) = prior := rfl

private theorem headValue (h prior : Nat) : evaluate offerHead (tape h prior) = h + 1 := by
  rw [offerHead,unaryValue] <;> rfl

private theorem preferValue (h prior : Nat) :
    evaluate preferHead (tape h prior) = if h + 1 < prior then 1 else 0 := by
  change evaluate ltTest (List.Vector.ofFn (fun i : Fin 2 =>
    evaluate ((![offerHead,.projection 1] : Fin 2 → Program 2) i) (tape h prior))) = _
  rw [vectorTwo]
  change evaluate ltTest (evaluate offerHead (tape h prior) ::ᵥ prior ::ᵥ nil) = _
  rw [headValue,exactLessThanEvaluation]

/-- Same original ordered one-cell optional update. No sentinel collides
with a real offered zero. Comparing successor codes preserves order. -/
theorem stepValue (h : Nat) (tail : Option Nat) :
    evaluate minimumStep (h ::ᵥ encodeState tail ::ᵥ nil) =
      encodeState (some (tail.elim h (min h))) := by
  cases tail with
  | none =>
    change evaluate minimumStep (tape h 0) = h + 1
    simp only [minimumStep,evalBranch,priorValue,if_true,headValue]
  | some k =>
    change evaluate minimumStep (tape h (k + 1)) = (min h k) + 1
    have priorPresent : k + 1 ≠ 0 := Nat.succ_ne_zero k
    by_cases smaller : h < k
    · have encoded : h + 1 < k + 1 := Nat.succ_lt_succ smaller
      simp [minimumStep,evalBranch,priorValue,priorPresent,headValue,preferValue,encoded,
        Nat.min_eq_left (Nat.le_of_lt smaller)]
    · have encoded : ¬ h + 1 < k + 1 := fun hp => smaller (Nat.lt_of_succ_lt_succ hp)
      simp [minimumStep,evalBranch,priorValue,priorPresent,headValue,preferValue,encoded,
        Nat.min_eq_right (Nat.le_of_not_gt smaller)]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericStepProof
