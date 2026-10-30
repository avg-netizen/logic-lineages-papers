module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteStepTargets
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Actual local rank forcing, with no exponent bound or invariant correctness field. -/
def groupInfiniteFiniteStepUlmRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G]
    (S : AddSubgroup G), Infinite S → Finite (pStep p S) →
      Module.rank (ZMod p) (UlmLayer p S) = Cardinal.aleph0

end LogicLineages.ModelsAlgebra.PGroups.Targets
