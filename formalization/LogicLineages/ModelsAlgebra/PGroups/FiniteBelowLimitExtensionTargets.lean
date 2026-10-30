module
public import LogicLineages.ModelsAlgebra.PGroups.BelowLimitExtensionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupFiniteBelowLimitExtension : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime],
    (∀ y : G, ∃ n : ℕ, p^n • y = 0) → (∀ y : H, ∃ n : ℕ, p^n • y = 0) →
    ∀ (D : AddSubgroup G) [Finite D] (B : AddSubgroup G) (C : AddSubgroup H)
      (f : B ≃+ C) (δ : Ordinal.{v}), Order.IsSuccLimit δ → ∀ hBD : B ≤ D,
      D ⊓ transfiniteFiltration p δ ≤ B →
      (∀ (b : B) (β : Ordinal.{v}), β ≤ δ →
        ((f b:H) ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
          (b:G) ∈ (transfiniteFiltration p β : AddSubgroup G))) →
      (∀ α : Ordinal.{v}, α < δ →
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤
          Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))) →
      ∃ F : D →+ H, Function.Injective F ∧
        (∀ b : B, F ⟨b,hBD b.property⟩ = (f b:H)) ∧
        ∀ (y : D) (β : Ordinal.{v}), β ≤ δ →
          (F y ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
            (y:G) ∈ (transfiniteFiltration p β : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
