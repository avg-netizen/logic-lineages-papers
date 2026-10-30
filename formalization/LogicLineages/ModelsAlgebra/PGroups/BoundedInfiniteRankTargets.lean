module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTailTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def groupBoundedInfiniteRankExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] [Infinite G] (N : ℕ),
    (∀ x : G, p^N • x = 0) → ∃ j : Fin N,
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val : AddSubgroup G)) = Cardinal.aleph0

end LogicLineages.ModelsAlgebra.PGroups.Targets
