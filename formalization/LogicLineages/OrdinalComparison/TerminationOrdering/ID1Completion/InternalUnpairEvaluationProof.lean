module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector InternalUnpair
open InternalSquareRootEvaluationProof InternalArithmeticProgramsEvaluationProof
open InternalLessThanEvaluationProof InternalAcceptanceCalibrationProof
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)

theorem rootSquareEvaluation (n : Nat) :
    evaluate rootSquare (n ::ᵥ List.Vector.nil) = Nat.sqrt n * Nat.sqrt n := by
  change evaluate InternalArithmeticPrograms.multiplication (List.Vector.ofFn fun i : Fin 2 =>
    evaluate (((Fin.cons InternalSquareRoot.root (Fin.cons InternalSquareRoot.root Fin.elim0)) : Fin 2 → Program 1) i)
      (n ::ᵥ List.Vector.nil)) = _
  rw [vectorTwo]
  change evaluate InternalArithmeticPrograms.multiplication
    (evaluate InternalSquareRoot.root (n ::ᵥ List.Vector.nil) ::ᵥ
      evaluate InternalSquareRoot.root (n ::ᵥ List.Vector.nil) ::ᵥ List.Vector.nil) = _
  rw [exactMultiplicationEvaluation,exactSquareRootEvaluation]

theorem residualEvaluation (n : Nat) :
    evaluate residual (n ::ᵥ List.Vector.nil) = n - Nat.sqrt n * Nat.sqrt n := by
  change evaluate InternalEqualityTest.subtract (List.Vector.ofFn fun i : Fin 2 =>
    evaluate (((Fin.cons rootSquare (Fin.cons (Program.projection (0 : Fin 1)) Fin.elim0)) : Fin 2 → Program 1) i)
      (n ::ᵥ List.Vector.nil)) = _
  rw [vectorTwo]
  change evaluate InternalEqualityTest.subtract
    (evaluate rootSquare (n ::ᵥ List.Vector.nil) ::ᵥ n ::ᵥ List.Vector.nil) = _
  rw [exactSubtractionEvaluation,rootSquareEvaluation]

theorem residualBelowRootEvaluation (n : Nat) :
    evaluate residualBelowRoot (n ::ᵥ List.Vector.nil) =
      if n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n then 1 else 0 := by
  change evaluate InternalLessThan.ltTest (List.Vector.ofFn fun i : Fin 2 =>
    evaluate (((Fin.cons residual (Fin.cons InternalSquareRoot.root Fin.elim0)) : Fin 2 → Program 1) i)
      (n ::ᵥ List.Vector.nil)) = _
  rw [vectorTwo]
  change evaluate InternalLessThan.ltTest
    (evaluate residual (n ::ᵥ List.Vector.nil) ::ᵥ
      evaluate InternalSquareRoot.root (n ::ᵥ List.Vector.nil) ::ᵥ List.Vector.nil) = _
  rw [exactLessThanEvaluation,residualEvaluation,exactSquareRootEvaluation]

theorem residualMinusRootEvaluation (n : Nat) :
    evaluate residualMinusRoot (n ::ᵥ List.Vector.nil) = n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n := by
  change evaluate InternalEqualityTest.subtract (List.Vector.ofFn fun i : Fin 2 =>
    evaluate (((Fin.cons InternalSquareRoot.root (Fin.cons residual Fin.elim0)) : Fin 2 → Program 1) i)
      (n ::ᵥ List.Vector.nil)) = _
  rw [vectorTwo]
  change evaluate InternalEqualityTest.subtract
    (evaluate InternalSquareRoot.root (n ::ᵥ List.Vector.nil) ::ᵥ
      evaluate residual (n ::ᵥ List.Vector.nil) ::ᵥ List.Vector.nil) = _
  rw [exactSubtractionEvaluation,exactSquareRootEvaluation,residualEvaluation]

/-- All natural inputs, including zero; this is separate from the internal inverse. -/
theorem exactUnpairEvaluation : InternalUnpairEvaluationTargets.ExactUnpairEvaluation := by
  intro n
  constructor
  · unfold InternalUnpair.left
    rw [evalBranch,residualBelowRootEvaluation,exactSquareRootEvaluation,residualEvaluation]
    by_cases h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n <;> simp [Nat.unpair,h]
  · unfold InternalUnpair.right
    rw [evalBranch,residualBelowRootEvaluation,residualMinusRootEvaluation,exactSquareRootEvaluation]
    by_cases h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n <;> simp [Nat.unpair,h]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationProof
