module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Nat.Prime.Defs
public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtensionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupSuccessorPreservingExtension : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime]
    (B : AddSubgroup G) (x : G) (α δ : Ordinal.{v}),
    (∀ y : G, ∃ n : ℕ, p^n • y = 0) → (∀ y : H, ∃ n : ℕ, p^n • y = 0) →
    α + 1 + 1 ≤ δ → x ∉ B → ∀ hpx : p • x ∈ B,
    ∀ (f : B →+ H), Function.Injective f →
    (∀ (b : B) (β : Ordinal.{v}), β ≤ δ →
      (f b ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
        (b : G) ∈ (transfiniteFiltration p β : AddSubgroup G))) →
    x ∈ (transfiniteFiltration p α : AddSubgroup G) →
    x ∉ (transfiniteFiltration p (α + 1) : AddSubgroup G) →
    p • x ∈ (transfiniteFiltration p (α + 1) : AddSubgroup G) →
    p • x ∉ (transfiniteFiltration p (α + 1 + 1) : AddSubgroup G) →
    (∀ b : B, ∀ β : Ordinal.{v},
      x + b ∈ (transfiniteFiltration p β : AddSubgroup G) →
      x ∈ (transfiniteFiltration p β : AddSubgroup G)) →
    (∀ b : B,
      (∀ c : B, ∀ β : Ordinal.{v},
        x + c ∈ (transfiniteFiltration p β : AddSubgroup G) →
        x + b ∈ (transfiniteFiltration p β : AddSubgroup G)) →
      ∀ β : Ordinal.{v}, p • (x + b) ∈ (transfiniteFiltration p β : AddSubgroup G) →
        p • x ∈ (transfiniteFiltration p β : AddSubgroup G)) →
    ∃ F : ↥(B ⊔ AddSubgroup.zmultiples x) →+ H, Function.Injective F ∧
      (∀ b : B, F ⟨b,(le_sup_left : B ≤ B ⊔ AddSubgroup.zmultiples x) b.property⟩ = f b) ∧
      ∀ (y : ↥(B ⊔ AddSubgroup.zmultiples x)) (β : Ordinal.{v}), β ≤ δ →
        (F y ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
          (y : G) ∈ (transfiniteFiltration p β : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
