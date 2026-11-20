module

public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

namespace LogicLineages.PersistentMarking.OrdinalCountablePrefixOmegaTargets
open scoped Ordinal

def CountablePrefixIffBelowOmegaOne : Prop :=
  ∀ o : Ordinal.{0}, Countable {β : Ordinal.{0} // β < o} ↔ o < ω₁

end LogicLineages.PersistentMarking.OrdinalCountablePrefixOmegaTargets
