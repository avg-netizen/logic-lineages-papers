module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalOneResponseDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth

def terminalOneResponse : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) → (∀ x : H, ∃ k : ℕ, p^k • x = 0) →
    ∀ (D : AddSubgroup G) [Finite D] (B : AddSubgroup G) (C : AddSubgroup H)
      (f : B ≃+ C) (δ : Ordinal.{0}), δ=0 ∨ Order.IsSuccLimit δ → ∀ hBD : B ≤ D,
    (∀ (b : B) (β : Ordinal.{0}), β ≤ δ →
      ((f b:H) ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
        (b:G) ∈ (transfiniteFiltration p β : AddSubgroup G))) →
    (∀ α < δ,
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))) →
    ∀ (n : ℕ) (b : Fin n → (transfiniteFiltration p δ : AddSubgroup G))
      (a : Fin n → (transfiniteFiltration p δ : AddSubgroup H))
      (hb : ∀ i, (b i:G) ∈ B),
    (∀ x : G, x ∈ B → x ∈ (transfiniteFiltration p δ : AddSubgroup G) → ∃ i, (b i:G)=x) →
    (∀ i, (a i:H) = (f ⟨b i,hb i⟩:H)) → BackAndForth (1:Ordinal.{0}) a b →
    ∃ F : D →+ H, Function.Injective F ∧
      (∀ z : B, F ⟨z,hBD z.property⟩ = (f z:H)) ∧
      ∀ (y : D) (β : Ordinal.{0}), β ≤ δ →
        (F y ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
          (y:G) ∈ (transfiniteFiltration p β : AddSubgroup G))
end LogicLineages.ModelsAlgebra.PGroups.Targets
