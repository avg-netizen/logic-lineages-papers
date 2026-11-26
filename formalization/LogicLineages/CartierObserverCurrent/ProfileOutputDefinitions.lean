module
public import LogicLineages.CartierObserverCurrent.ProfileDescentDefinitions
public import LogicLineages.CartierObserverCurrent.FractionSeriesDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ProfileOutput
open SplittingRoots

/-- Literal source output sum, not defined to be an expansion coefficient. -/
noncomputable def value (d : Nat) (b : Root d → FieldAt d) : FieldAt d := by
  classical
  letI : Fintype (Root d) := by unfold Root; infer_instance
  exact ∑ z : Root d, b z / z.val
end LogicLineages.CartierObserverCurrent.ProfileOutput
