module

public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Actual top socle of a nonzero-length cyclic p-group, not a dimension
field or an assumed representative supplier. -/
def groupCyclicTopSocleIsomorphism : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 0 < k →
    Nonempty (ZMod p ≃+ pSocle p (⊤ : AddSubgroup (ZMod (p ^ k))))

end LogicLineages.ModelsAlgebra.PGroups.Targets
