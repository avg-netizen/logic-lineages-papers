module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedTailCategoricityDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def boundedTailCategoricity : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ x : H, ∃ k : ℕ, p^k • x = 0) →
    ∀ (δ : Ordinal.{0}) (N : ℕ),
    (∀ x : (transfiniteFiltration p δ : AddSubgroup G), p^N • x = 0) →
    ((transfiniteFiltration p δ : AddSubgroup G) ≃+
      (transfiniteFiltration p δ : AddSubgroup H)) →
    (∀ α < δ,
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))) →
    Nonempty (G ≃+ H)
end LogicLineages.ModelsAlgebra.PGroups.Targets
