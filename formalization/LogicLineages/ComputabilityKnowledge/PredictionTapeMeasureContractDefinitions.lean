module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClassDefinitions
public import Mathlib.Data.Nat.Cast.WithTop
@[expose] public section
/-! The source extended-natural measure, defined by the first failed positive
threshold, or infinity if no threshold fails. For monotone level bounds the
proved contract is precisely zero / maximum successful level / infinity.
This mathematical definition makes no computability assertion. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContract
open PredictionGame PredictionTapeRuntimeClass

noncomputable def height (levels : Nat → Nat → Nat) (p : Policy) : WithTop Nat := by
  classical
  exact if h : ∃ m : Nat, 1 ≤ m ∧ ¬ Threshold p (levels m) then
    ((Nat.find h - 1 : Nat) : WithTop Nat) else ⊤

end LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContract
