module
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteStepTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Finite genuine tail invariants force an actual finite tail subgroup. -/
def groupFiniteTailFromRanks : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (N : ℕ),
    (∀ g : G, p ^ N • g = 0) → ∀ k : ℕ, k ≤ N →
    (∀ j : ℕ, k ≤ j → j < N →
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0) →
    Finite (finiteFiltration p k : AddSubgroup G)

/-- An actual infinite Ulm rank cannot occur in a finite filtration subgroup. -/
def groupInfiniteUlmInfiniteFiltration : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (j : ℕ),
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) = Cardinal.aleph0 →
    Infinite (finiteFiltration p j : AddSubgroup G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
