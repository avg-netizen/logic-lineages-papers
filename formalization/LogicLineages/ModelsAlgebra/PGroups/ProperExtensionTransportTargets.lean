module
public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtensionTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupProperExtensionTransport : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime],
    (∀ y : G, ∃ n : ℕ, p^n • y = 0) → (∀ y : H, ∃ n : ℕ, p^n • y = 0) →
    ∀ (B : AddSubgroup G) (x : G), p • x ∈ B →
    ∀ (f : B →+ H) (w : H) (α δ : Ordinal.{v}),
    (∀ (b : B) (β : Ordinal.{v}), β ≤ δ →
      (f b ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
        (b : G) ∈ (transfiniteFiltration p β : AddSubgroup G))) →
    x ∈ (transfiniteFiltration p α : AddSubgroup G) →
    x ∉ (transfiniteFiltration p (α+1) : AddSubgroup G) →
    w ∈ (transfiniteFiltration p α : AddSubgroup H) →
    w ∉ (transfiniteFiltration p (α+1) : AddSubgroup H) →
    (∀ (b : B) (β : Ordinal.{v}), x + b ∈ (transfiniteFiltration p β : AddSubgroup G) →
      x ∈ (transfiniteFiltration p β : AddSubgroup G)) →
    (∀ (b : B) (β : Ordinal.{v}), w + f b ∈ (transfiniteFiltration p β : AddSubgroup H) →
      w ∈ (transfiniteFiltration p β : AddSubgroup H)) →
    ∀ F : ↥(B ⊔ AddSubgroup.zmultiples x) →+ H,
    (∀ b : B, F ⟨b,(le_sup_left : B ≤ B ⊔ AddSubgroup.zmultiples x) b.property⟩ = f b) →
    F ⟨x,(le_sup_right : AddSubgroup.zmultiples x ≤ B ⊔ AddSubgroup.zmultiples x)
      (AddSubgroup.mem_zmultiples x)⟩ = w →
    ∀ (y : ↥(B ⊔ AddSubgroup.zmultiples x)) (β : Ordinal.{v}), β ≤ δ →
      (F y ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
        (y : G) ∈ (transfiniteFiltration p β : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
