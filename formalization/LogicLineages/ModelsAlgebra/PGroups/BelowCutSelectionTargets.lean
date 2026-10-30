module
public import LogicLineages.ModelsAlgebra.PGroups.CosetNormalizationTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupBelowCutSelection : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ),
    (∀ y : G, ∃ n : ℕ, p^n • y = 0) →
    ∀ (B D : AddSubgroup G) [Finite B] (δ : Ordinal.{v}),
      B ≤ D → ¬D ≤ B → D ⊓ transfiniteFiltration p δ ≤ B →
      ∃ (x : G) (α : Ordinal.{v}), x ∈ D ∧ x ∉ B ∧ p • x ∈ B ∧
        x ∉ (transfiniteFiltration p δ : AddSubgroup G) ∧ α < δ ∧
        x ∈ (transfiniteFiltration p α : AddSubgroup G) ∧
        x ∉ (transfiniteFiltration p (α+1) : AddSubgroup G) ∧
        (∀ (b : B) (β : Ordinal.{v}), x+b ∈ (transfiniteFiltration p β : AddSubgroup G) →
          x ∈ (transfiniteFiltration p β : AddSubgroup G)) ∧
        ∀ b : B,
          (∀ (c : B) (β : Ordinal.{v}), x+c ∈ (transfiniteFiltration p β : AddSubgroup G) →
            x+b ∈ (transfiniteFiltration p β : AddSubgroup G)) →
          ∀ β : Ordinal.{v}, p • (x+b) ∈ (transfiniteFiltration p β : AddSubgroup G) →
            p • x ∈ (transfiniteFiltration p β : AddSubgroup G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
