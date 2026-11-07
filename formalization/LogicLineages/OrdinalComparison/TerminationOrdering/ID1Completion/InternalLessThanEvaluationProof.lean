module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
open InternalLessThan InternalAcceptance LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalEqualityTestEvaluationProof InternalAcceptanceCalibrationProof

theorem exactLessThanEvaluation : InternalLessThanTargets.ExactLessThanEvaluation := by
  intro x y
  unfold ltTest
  rw [evalBranch,exactSubtractionEvaluation]
  have hz : evaluate (constantZero 2) (x ::ᵥ y ::ᵥ List.Vector.nil) = 0 := rfl
  have ho : evaluate (constantOne 2) (x ::ᵥ y ::ᵥ List.Vector.nil) = 1 := by
    simp [constantOne,constantZero,evaluate]
  rw [hz,ho]
  split_ifs <;> omega

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
