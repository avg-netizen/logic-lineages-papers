module
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryUlmClassificationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def countablePrimaryUlmClassification : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ x : H, ∃ k : ℕ, p^k • x = 0) →
    (Nonempty (G ≃+ H) ↔
      (∀ α : Ordinal.{0},
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) =
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))) ∧
      divisibleSocleRank p G = divisibleSocleRank p H)
end LogicLineages.ModelsAlgebra.PGroups.Targets
