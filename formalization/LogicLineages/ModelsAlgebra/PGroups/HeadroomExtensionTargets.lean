module
public import LogicLineages.ModelsAlgebra.PGroups.HeadroomExtensionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def oneUnitHeadroomExtension : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    ∀ (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (f : B ≃+ C)
      (δ α ρ : Ordinal.{v}), δ ≤ α → α ≤ ρ →
    (∀ b : B, ∀ β ≤ δ,
      (f b : H) ∈ transfiniteFiltration p β ↔ (b : G) ∈ transfiniteFiltration p β) →
    (∀ b : B, ∀ β ≤ ρ+1,
      (b : G) ∈ transfiniteFiltration p β → (f b : H) ∈ transfiniteFiltration p β) →
    ∀ (x : G), x ∉ B → x ∈ transfiniteFiltration p α →
    (x ∉ transfiniteFiltration p (α+1) ∨ α = ρ) →
    (∀ b : B, ∀ β : Ordinal.{v},
      x+b ∈ transfiniteFiltration p β → x ∈ transfiniteFiltration p β) →
    ∀ hpx : p • x ∈ B,
    Infinite (pSocle p (transfiniteFiltration p α : AddSubgroup H)) →
    ∃ F : ↥(B ⊔ AddSubgroup.zmultiples x) →+ H, Function.Injective F ∧
      (∀ b : B, F ⟨b, (le_sup_left : B ≤ B ⊔ AddSubgroup.zmultiples x) b.property⟩ = f b) ∧
      (∀ z : ↥(B ⊔ AddSubgroup.zmultiples x), ∀ β ≤ δ,
        F z ∈ transfiniteFiltration p β ↔ (z : G) ∈ transfiniteFiltration p β) ∧
      (∀ z : ↥(B ⊔ AddSubgroup.zmultiples x), ∀ β ≤ ρ,
        (z : G) ∈ transfiniteFiltration p β → F z ∈ transfiniteFiltration p β)
end LogicLineages.ModelsAlgebra.PGroups.Targets
