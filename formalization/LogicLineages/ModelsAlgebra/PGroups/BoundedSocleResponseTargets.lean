module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedSocleResponseDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def boundedSocleOddResponse : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ y : H, ∃ k : ℕ, p^k • y = 0) →
    ∀ σ : Ordinal.{0},
    (∀ α < σ, Infinite (pSocle p (transfiniteFiltration p α : AddSubgroup H))) →
    ∀ (D : AddSubgroup G) [Finite D] (B : AddSubgroup G) (C : AddSubgroup H)
      (f : B ≃+ C) (δ : Ordinal.{0}), (δ = 0 ∨ Order.IsSuccLimit δ) →
    ∀ hBD : B ≤ D, δ+(Nat.card D : Ordinal.{0}) < σ →
    (∀ b : B, ∀ β ≤ δ,
      (f b : H) ∈ transfiniteFiltration p β ↔ (b : G) ∈ transfiniteFiltration p β) →
    (∀ b : B, ∀ β ≤ δ + (Nat.card D : Ordinal.{0}),
      (b : G) ∈ transfiniteFiltration p β → (f b : H) ∈ transfiniteFiltration p β) →
    (∀ α : Ordinal.{0}, α < δ →
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))) →
    ∃ F : D →+ H, Function.Injective F ∧
      (∀ b : B, F ⟨b,hBD b.property⟩ = f b) ∧
      ∀ z : D, ∀ β ≤ δ,
        F z ∈ transfiniteFiltration p β ↔ (z : G) ∈ transfiniteFiltration p β

def boundedSocleGapResponse : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ y : H, ∃ k : ℕ, p^k • y = 0) →
    ∀ σ : Ordinal.{0},
    (∀ α < σ, Infinite (pSocle p (transfiniteFiltration p α : AddSubgroup H))) →
    ∀ (D : AddSubgroup G) [Finite D] (B : AddSubgroup G) (C : AddSubgroup H)
      (f : B ≃+ C) (lam : Ordinal.{0}),
    D ⊓ transfiniteFiltration p lam = D ⊓ transfiniteFiltration p (lam+1) →
    ∀ hBD : B ≤ D, (lam+1)+(Nat.card D : Ordinal.{0}) < σ →
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

def boundedSocleEvenResponse : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ y : H, ∃ k : ℕ, p^k • y = 0) →
    ∀ σ : Ordinal.{0},
    (∀ α < σ, Infinite (pSocle p (transfiniteFiltration p α : AddSubgroup H))) →
    ∀ (D : AddSubgroup G) [Finite D] (B : AddSubgroup G) (C : AddSubgroup H)
      (f : B ≃+ C) (δ : Ordinal.{0}), ∀ hBD : B ≤ D, δ+Ordinal.omega0 ≤ σ →
    (∀ b : B, ∀ β ≤ δ+Ordinal.omega0,
      (f b : H) ∈ transfiniteFiltration p β ↔ (b : G) ∈ transfiniteFiltration p β) →
    (∀ α : Ordinal.{0}, α < δ+Ordinal.omega0 →
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))) →
    ∃ F : D →+ H, Function.Injective F ∧
      (∀ b : B, F ⟨b,hBD b.property⟩ = f b) ∧
      (∀ z : D, ∀ β ≤ δ,
        F z ∈ transfiniteFiltration p β ↔ (z : G) ∈ transfiniteFiltration p β) ∧
      (∀ z : D, ∀ β ≤ δ+Ordinal.omega0,
        F z ∈ transfiniteFiltration p β → (z : G) ∈ transfiniteFiltration p β)

end LogicLineages.ModelsAlgebra.PGroups.Targets
