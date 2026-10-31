module
public import LogicLineages.ModelsAlgebra.PGroups.StableTailCategoricityDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def stableTailCategoricity : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ x : H, ∃ k : ℕ, p^k • x = 0) →
    ∀ α : Ordinal.{0}, StableAt p G α → StableAt p H α →
    (∀ β < α,
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p β : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p β : AddSubgroup H))) →
    Module.rank (ZMod p) (pSocle p (transfiniteFiltration p α : AddSubgroup G)) =
      Module.rank (ZMod p) (pSocle p (transfiniteFiltration p α : AddSubgroup H)) →
    Nonempty (G ≃+ H)
end LogicLineages.ModelsAlgebra.PGroups.Targets
