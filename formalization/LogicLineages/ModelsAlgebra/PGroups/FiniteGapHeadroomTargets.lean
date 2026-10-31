module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteGapHeadroomDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def finiteGapResponseExtension : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ y : H, ∃ k : ℕ, p^k • y = 0) →
    ∀ (e : DirectSum ℕ (fun _ => PrueferModel p) →+ H), Function.Injective e →
    ∀ (D : AddSubgroup G) [Finite D] (B : AddSubgroup G) (C : AddSubgroup H)
      (f : B ≃+ C) (lam : Ordinal.{0}),
    D ⊓ transfiniteFiltration p lam = D ⊓ transfiniteFiltration p (lam+1) →
    ∀ hBD : B ≤ D,
    (∀ b : B, ∀ β ≤ lam+1,
      (f b : H) ∈ transfiniteFiltration p β ↔ (b : G) ∈ transfiniteFiltration p β) →
    (∀ b : B, ∀ β ≤ lam+1 + (Nat.card D : Ordinal.{0}),
      (b : G) ∈ transfiniteFiltration p β → (f b : H) ∈ transfiniteFiltration p β) →
    (∀ α : Ordinal.{0}, α < lam →
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))) →
    ∃ F : D →+ H, Function.Injective F ∧
      (∀ b : B, F ⟨b,hBD b.property⟩ = f b) ∧
      ∀ z : D, ∀ β ≤ lam+1,
        F z ∈ transfiniteFiltration p β ↔ (z : G) ∈ transfiniteFiltration p β

end LogicLineages.ModelsAlgebra.PGroups.Targets
