module
public import LogicLineages.ModelsAlgebra.PGroups.SocleGapExtensionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupBelowLimitExtension : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime],
    (∀ y : G, ∃ n : ℕ, p^n • y = 0) → (∀ y : H, ∃ n : ℕ, p^n • y = 0) →
    ∀ (B D : AddSubgroup G) (C : AddSubgroup H) [Finite B] (f : B ≃+ C) (δ : Ordinal.{v}),
      Order.IsSuccLimit δ → B ≤ D → ¬D ≤ B → D ⊓ transfiniteFiltration p δ ≤ B →
      (∀ (b : B) (β : Ordinal.{v}), β ≤ δ →
        ((f b:H) ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
          (b:G) ∈ (transfiniteFiltration p β : AddSubgroup G))) →
      (∀ α : Ordinal.{v}, α < δ →
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤
          Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))) →
      ∃ x : G, x ∈ D ∧ x ∉ B ∧ p • x ∈ B ∧
        ∃ F : ↥(B ⊔ AddSubgroup.zmultiples x) →+ H, Function.Injective F ∧
          (∀ b : B, F ⟨b,(le_sup_left : B ≤ B ⊔ AddSubgroup.zmultiples x) b.property⟩ = (f b:H)) ∧
          ∀ (y : ↥(B ⊔ AddSubgroup.zmultiples x)) (β : Ordinal.{v}), β ≤ δ →
            (F y ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
              (y:G) ∈ (transfiniteFiltration p β : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
