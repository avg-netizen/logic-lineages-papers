module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeValuesThinProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalSquareRootEvaluationProof (exactSquareRootEvaluation)
open InternalArithmeticProgramsEvaluationProof (vectorTwo exactMultiplicationEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalAcceptanceCalibrationProof (evalBranch)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparseDecode NumberedWindowInternalSparseDecodeTargets

private theorem squareValue (n : Nat) :
    evaluate rootSquare (n ::ᵥ nil) = Nat.sqrt n * Nat.sqrt n := by
  simp only [rootSquare,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [exactMultiplicationEvaluation,exactSquareRootEvaluation]

private theorem leftValue (n : Nat) :
    evaluate leftCandidate (n ::ᵥ nil) = n - Nat.sqrt n * Nat.sqrt n := by
  simp only [leftCandidate,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one]
  change evaluate InternalEqualityTest.subtract (evaluate rootSquare (n ::ᵥ nil) ::ᵥ n ::ᵥ nil) = _
  rw [exactSubtractionEvaluation,squareValue]

private theorem rightValue (n : Nat) :
    evaluate rightCandidate (n ::ᵥ nil) = Nat.sqrt n - (n - Nat.sqrt n * Nat.sqrt n) := by
  simp only [rightCandidate,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [exactSubtractionEvaluation,exactSquareRootEvaluation,leftValue]

theorem candidates : CandidateValues := by
  intro n
  exact ⟨leftValue n,rightValue n⟩

private theorem gapValue (n : Nat) :
    evaluate gap (n ::ᵥ nil) = if Nat.sqrt n < n - Nat.sqrt n * Nat.sqrt n then 1 else 0 := by
  simp only [gap,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [exactLessThanEvaluation,exactSquareRootEvaluation,leftValue]

theorem guardValue : GuardValue := by
  intro n
  unfold good
  rw [evalBranch,gapValue]
  change (if (if Nat.sqrt n < n - Nat.sqrt n * Nat.sqrt n then 1 else 0) = (0 : Nat)
    then 1 else 0) = _
  by_cases h : n - Nat.sqrt n * Nat.sqrt n ≤ Nat.sqrt n
  · simp [h,Nat.not_lt.mpr h]
  · simp [h,Nat.lt_of_not_ge h]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeValuesThinProof
