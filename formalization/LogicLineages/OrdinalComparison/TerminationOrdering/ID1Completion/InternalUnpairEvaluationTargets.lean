module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairDefinitions
public import Mathlib.Data.Nat.Pairing
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Separate all-input standard evaluation calibration to the literal Nat.unpair.
This external theorem is never used as an internal-calculus reflection rule. -/
def ExactUnpairEvaluation : Prop :=
  ∀ n : Nat,
  evaluate InternalUnpair.left (n ::ᵥ List.Vector.nil) = (Nat.unpair n).1 ∧
  evaluate InternalUnpair.right (n ::ᵥ List.Vector.nil) = (Nat.unpair n).2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationTargets
