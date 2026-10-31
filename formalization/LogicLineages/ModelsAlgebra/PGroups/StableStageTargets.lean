module
public import LogicLineages.ModelsAlgebra.PGroups.StableStageDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def primaryStableStage : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → ∀ α : Ordinal.{0}, StableAt p G α →
    SubgroupDivisible (transfiniteFiltration p α : AddSubgroup G) ∧
    (transfiniteFiltration p α : AddSubgroup G) = divisiblePart G ∧
    ∀ β : Ordinal.{0}, α ≤ β →
      (transfiniteFiltration p β : AddSubgroup G) = divisiblePart G ∧
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p β : AddSubgroup G)) = 0
end LogicLineages.ModelsAlgebra.PGroups.Targets
