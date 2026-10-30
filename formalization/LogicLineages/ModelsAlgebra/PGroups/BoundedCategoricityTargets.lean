module
public import LogicLineages.ModelsAlgebra.PGroups.CyclicClassificationTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Genuine bounded classification by the actual finite Ulm Cardinal ranks.
No decomposition or invariant-correctness field is supplied as a premise. -/
def groupBoundedUlmCategoricity : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G H : Type) [AddCommGroup G] [AddCommGroup H] (N : ℕ),
    (∀ g : G, p ^ N • g = 0) → (∀ h : H, p ^ N • h = 0) →
    (∀ j : Fin N,
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val : AddSubgroup H))) →
    Nonempty (G ≃+ H)

end LogicLineages.ModelsAlgebra.PGroups.Targets
