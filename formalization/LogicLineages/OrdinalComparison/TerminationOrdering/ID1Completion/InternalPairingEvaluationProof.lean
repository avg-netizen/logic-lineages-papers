module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalPairing InternalArithmeticPrograms InternalArithmeticProgramsEvaluationProof
open InternalLessThanEvaluationProof InternalAcceptanceCalibrationProof

theorem squareFirstEvaluation (x y : Nat) :
    evaluate squareFirst (x ::ᵥ y ::ᵥ List.Vector.nil) = x*x := by
  change evaluate multiplication (List.Vector.ofFn fun _ : Fin 2 => x) = _
  rw [vectorTwo,exactMultiplicationEvaluation]

theorem squareSecondEvaluation (x y : Nat) :
    evaluate squareSecond (x ::ᵥ y ::ᵥ List.Vector.nil) = y*y := by
  change evaluate multiplication (List.Vector.ofFn fun _ : Fin 2 => y) = _
  rw [vectorTwo,exactMultiplicationEvaluation]

theorem squareFirstPlusFirstEvaluation (x y : Nat) :
    evaluate squareFirstPlusFirst (x ::ᵥ y ::ᵥ List.Vector.nil) = x*x+x := by
  change evaluate addition (List.Vector.ofFn fun i : Fin 2 =>
    evaluate (((Fin.cons squareFirst (Fin.cons (Program.projection (0 : Fin 2)) Fin.elim0)) : Fin 2 → Program 2) i)
      (x ::ᵥ y ::ᵥ List.Vector.nil)) = _
  rw [vectorTwo]
  change evaluate addition (evaluate squareFirst (x ::ᵥ y ::ᵥ List.Vector.nil) ::ᵥ x ::ᵥ List.Vector.nil) = _
  rw [exactAdditionEvaluation,squareFirstEvaluation]

theorem nonLessBranchEvaluation (x y : Nat) :
    evaluate nonLessBranch (x ::ᵥ y ::ᵥ List.Vector.nil) = x*x+x+y := by
  change evaluate addition (List.Vector.ofFn fun i : Fin 2 =>
    evaluate (((Fin.cons squareFirstPlusFirst (Fin.cons (Program.projection (1 : Fin 2)) Fin.elim0)) : Fin 2 → Program 2) i)
      (x ::ᵥ y ::ᵥ List.Vector.nil)) = _
  rw [vectorTwo]
  change evaluate addition (evaluate squareFirstPlusFirst (x ::ᵥ y ::ᵥ List.Vector.nil) ::ᵥ y ::ᵥ List.Vector.nil) = _
  rw [exactAdditionEvaluation,squareFirstPlusFirstEvaluation]

theorem lessBranchEvaluation (x y : Nat) :
    evaluate lessBranch (x ::ᵥ y ::ᵥ List.Vector.nil) = y*y+x := by
  change evaluate addition (List.Vector.ofFn fun i : Fin 2 =>
    evaluate (((Fin.cons squareSecond (Fin.cons (Program.projection (0 : Fin 2)) Fin.elim0)) : Fin 2 → Program 2) i)
      (x ::ᵥ y ::ᵥ List.Vector.nil)) = _
  rw [vectorTwo]
  change evaluate addition (evaluate squareSecond (x ::ᵥ y ::ᵥ List.Vector.nil) ::ᵥ x ::ᵥ List.Vector.nil) = _
  rw [exactAdditionEvaluation,squareSecondEvaluation]

/-- This equation names the pinned Mathlib function itself. -/
theorem exactPairingEvaluation : InternalPairingTargets.ExactPairingEvaluation := by
  intro x y
  unfold pairing
  rw [evalBranch,exactLessThanEvaluation,nonLessBranchEvaluation,lessBranchEvaluation]
  by_cases h : x < y <;> simp [h,Nat.pair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingEvaluationProof
