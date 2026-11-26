module
public import LogicLineages.OrdinalComparison.SourceTypes

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowComputabilityReading
open LogicLineages.OrdinalComparison.Source

/-- Relational reading of application at an admitted function: each actual
argument and its canonical output must satisfy the printed arrow implication. -/
def holds (app : Nat → Nat → Nat → Prop) (P : Nat → Prop) : Ty → Nat → Prop
  | .ground, q => P (2*q)
  | .arrow σ τ, q => ∀ u v, app q u v → holds app P σ u → holds app P τ v
end LogicLineages.PersistentMarking.NumberedWindowComputabilityReading
