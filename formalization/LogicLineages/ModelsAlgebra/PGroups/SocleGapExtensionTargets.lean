module
public import LogicLineages.ModelsAlgebra.PGroups.ProperSocleTransportTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtensionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupSocleGapPreservingExtension : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime]
    (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (x : G) (α δ : Ordinal.{v}),
    (∀ y : G, ∃ n : ℕ, p^n • y = 0) → (∀ y : H, ∃ n : ℕ, p^n • y = 0) →
    α+1+1 ≤ δ → x ∉ B → ∀ hpx : p • x ∈ B, ∀ f : B ≃+ C,
    (∀ (b : B) (β : Ordinal.{v}), β ≤ δ →
      ((f b:H) ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
        (b:G) ∈ (transfiniteFiltration p β : AddSubgroup G))) →
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H)) →
    x ∈ (transfiniteFiltration p α : AddSubgroup G) →
    x ∉ (transfiniteFiltration p (α+1) : AddSubgroup G) →
    p • x ∈ (transfiniteFiltration p (α+1+1) : AddSubgroup G) →
    (∀ (b : B) (β : Ordinal.{v}), x+b ∈ (transfiniteFiltration p β : AddSubgroup G) →
      x ∈ (transfiniteFiltration p β : AddSubgroup G)) →
    ∃ F : ↥(B ⊔ AddSubgroup.zmultiples x) →+ H, Function.Injective F ∧
      (∀ b : B, F ⟨b,(le_sup_left : B ≤ B ⊔ AddSubgroup.zmultiples x) b.property⟩ = (f b:H)) ∧
      ∀ (y : ↥(B ⊔ AddSubgroup.zmultiples x)) (β : Ordinal.{v}), β ≤ δ →
        (F y ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
          (y:G) ∈ (transfiniteFiltration p β : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
