module
public import LogicLineages.ModelsAlgebra.PGroups.CountableUlmDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Actual countable Ulm classification at a common proved zero-stage limit cut.
No extension, coherence, enumeration or classification law is a hypothesis.
General stabilization of arbitrary countable reduced groups remains separate. -/
def countableUlmAtZeroCut : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ n : ℕ, p^n • x = 0) → (∀ x : H, ∃ n : ℕ, p^n • x = 0) →
    ∀ δ : Ordinal.{0}, Order.IsSuccLimit δ →
    (transfiniteFiltration p δ : AddSubgroup G) = ⊥ →
    (transfiniteFiltration p δ : AddSubgroup H) = ⊥ →
    (∀ α < δ, Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))) →
    Nonempty (G ≃+ H)
/-- Strong finite-map extension version, with genuine finite height map as input. -/
def countableUlmExtendsAtZeroCut : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ n : ℕ, p^n • x = 0) → (∀ x : H, ∃ n : ℕ, p^n • x = 0) →
    ∀ δ : Ordinal.{0}, Order.IsSuccLimit δ →
    (transfiniteFiltration p δ : AddSubgroup G) = ⊥ →
    (transfiniteFiltration p δ : AddSubgroup H) = ⊥ →
    (∀ α < δ, Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))) →
    ∀ f : FiniteHeightIso p G H, ∃ e : G ≃+ H,
      (∀ x : f.domain, e x = (f.equiv x : H)) ∧
      ∀ (x : G) (α : Ordinal.{0}), e x ∈ transfiniteFiltration p α ↔ x ∈ transfiniteFiltration p α
end LogicLineages.ModelsAlgebra.PGroups.Targets
