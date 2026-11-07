module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootEvaluationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootEvaluationProof
open InternalSquareRoot LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalArithmeticProgramsEvaluationProof InternalLessThanEvaluationProof InternalAcceptanceCalibrationProof

theorem nextSquareEvaluation (n old : Nat) :
    evaluate nextSquare (n ::ᵥ old ::ᵥ List.Vector.nil) = (old+1)*(old+1) := by
  unfold nextSquare
  change evaluate InternalArithmeticPrograms.multiplication (List.Vector.ofFn (fun i : Fin 2 =>
    evaluate ((Fin.cons successorRoot (Fin.cons successorRoot Fin.elim0) : Fin 2 → Program 2) i)
      (n ::ᵥ old ::ᵥ List.Vector.nil))) = _
  rw [vectorTwo]
  change evaluate InternalArithmeticPrograms.multiplication ((old+1) ::ᵥ (old+1) ::ᵥ List.Vector.nil) = _
  exact exactMultiplicationEvaluation (old+1) (old+1)

theorem controlEvaluation (n old : Nat) :
    evaluate belowNextSquare (n ::ᵥ old ::ᵥ List.Vector.nil) =
      if n+1 < (old+1)*(old+1) then 1 else 0 := by
  unfold belowNextSquare
  change evaluate InternalLessThan.ltTest (List.Vector.ofFn (fun i : Fin 2 =>
    evaluate ((Fin.cons successorCounter (Fin.cons nextSquare Fin.elim0) : Fin 2 → Program 2) i)
      (n ::ᵥ old ::ᵥ List.Vector.nil))) = _
  rw [vectorTwo]
  change evaluate InternalLessThan.ltTest ((n+1) ::ᵥ
    evaluate nextSquare (n ::ᵥ old ::ᵥ List.Vector.nil) ::ᵥ List.Vector.nil) = _
  rw [nextSquareEvaluation,exactLessThanEvaluation]

theorem stepEvaluation (n old : Nat) :
    evaluate step (n ::ᵥ old ::ᵥ List.Vector.nil) =
      if n+1 < (old+1)*(old+1) then old else old+1 := by
  unfold step
  rw [evalBranch,controlEvaluation]
  change (if (if n+1 < (old+1)*(old+1) then 1 else 0) = 0 then old+1 else old) = _
  split_ifs <;> simp_all

theorem exactSquareRootRecurrence : InternalSquareRootEvaluationTargets.ExactSquareRootRecurrence := by
  constructor
  · rfl
  · intro n
    change evaluate step (n ::ᵥ evaluate root (n ::ᵥ List.Vector.nil) ::ᵥ List.Vector.nil) = _
    exact stepEvaluation n _

/-- Standard natural-number calibration only; the internal derivation files
do not import this module or use this theorem. -/
theorem exactSquareRootEvaluation : InternalSquareRootEvaluationTargets.ExactSquareRootEvaluation := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [exactSquareRootRecurrence.2,ih]
    split_ifs with h
    · exact Nat.eq_sqrt.mpr ⟨Nat.le_trans (Nat.sqrt_le n) (Nat.le_succ n), h⟩
    · apply Nat.eq_sqrt.mpr
      constructor
      · exact Nat.le_of_not_gt h
      · exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (Nat.lt_succ_sqrt n))
          (Nat.mul_self_lt_mul_self_iff.mpr (Nat.lt_succ_self (Nat.sqrt n+1)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootEvaluationProof
