module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalArithmeticProgramsEvaluationProof (exactAdditionEvaluation exactMultiplicationEvaluation vectorTwo)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparsePair NumberedWindowInternalSparsePairTargets

private theorem squareValue (x y : Nat) :
    evaluate squaredSum (x ::ᵥ y ::ᵥ nil) = (x+y)*(x+y) := by
  simp only [squaredSum,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [exactMultiplicationEvaluation,exactAdditionEvaluation]

theorem pairValue : PairValue := by
  intro x y
  simp only [NumberedWindowInternalSparsePair.pair,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one]
  change evaluate InternalArithmeticPrograms.addition
    (evaluate squaredSum (x ::ᵥ y ::ᵥ nil) ::ᵥ x ::ᵥ nil) = _
  rw [exactAdditionEvaluation,squareValue]
  rfl

theorem consValue : FieldConsValue := by
  intro x tail
  change Nat.succ (evaluate NumberedWindowInternalSparsePair.pair (x ::ᵥ tail ::ᵥ nil)) = _
  exact congrArg Nat.succ (pairValue x tail)
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
