module
public import LogicLineages.ModelsAlgebra.PGroups.HighRootExtensionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def highRootExtension : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime]
    (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (f : B ≃+ C)
    (δ : Ordinal.{v}),
    (∀ b : B, ∀ β ≤ δ,
      (f b : H) ∈ transfiniteFiltration p β ↔ (b : G) ∈ transfiniteFiltration p β) →
    ∀ (x : G), x ∉ B → x ∈ transfiniteFiltration p δ →
    ∀ hpx : p • x ∈ B,
    (f ⟨p • x, hpx⟩ : H) ∈ transfiniteFiltration p (δ + 1) →
    Infinite (pSocle p (transfiniteFiltration p δ : AddSubgroup H)) →
    ∃ F : ↥(B ⊔ AddSubgroup.zmultiples x) →+ H, Function.Injective F ∧
      (∀ b : B, F ⟨b, (le_sup_left : B ≤ B ⊔ AddSubgroup.zmultiples x) b.property⟩ = f b) ∧
      (∀ z : ↥(B ⊔ AddSubgroup.zmultiples x), ∀ β ≤ δ,
        F z ∈ transfiniteFiltration p β ↔ (z : G) ∈ transfiniteFiltration p β)

end LogicLineages.ModelsAlgebra.PGroups.Targets
