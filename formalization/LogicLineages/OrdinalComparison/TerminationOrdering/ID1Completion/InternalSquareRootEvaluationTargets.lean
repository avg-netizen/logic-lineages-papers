module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootDefinitions
public import Mathlib.Data.Nat.Sqrt
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootEvaluationTargets
open InternalSquareRoot LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
/-- Standard evaluation alone. No internal proof imports this calibration. -/
def ExactSquareRootRecurrence : Prop :=
  evaluate root (0 ::ᵥ List.Vector.nil) = 0 ∧
  ∀ n : Nat, evaluate root ((n+1) ::ᵥ List.Vector.nil) =
    if n+1 < (evaluate root (n ::ᵥ List.Vector.nil)+1) *
      (evaluate root (n ::ᵥ List.Vector.nil)+1)
    then evaluate root (n ::ᵥ List.Vector.nil)
    else evaluate root (n ::ᵥ List.Vector.nil)+1
/-- External calibration to the pinned Nat.sqrt used by Nat.unpair.
This is not an object-calculus reflection rule. -/
def ExactSquareRootEvaluation : Prop :=
  ∀ n : Nat, evaluate root (n ::ᵥ List.Vector.nil) = Nat.sqrt n
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootEvaluationTargets
