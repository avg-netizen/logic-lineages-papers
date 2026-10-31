module
public import LogicLineages.ModelsAlgebra.PGroups.FinitePrueferEmbeddingDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Actual characters separate each nonzero element of any primary group. -/
def primaryPrueferSeparation : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    ∀ x : G, x ≠ 0 → ∃ f : G →+ PrueferModel p, f x ≠ 0
/-- Finite primary groups embed in a genuinely finite product of the literal Prüfer model. -/
def finitePrueferEmbedding : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Finite G],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    ∃ n : ℕ, ∃ f : G →+ (Fin n → PrueferModel p), Function.Injective f
end LogicLineages.ModelsAlgebra.PGroups.Targets
