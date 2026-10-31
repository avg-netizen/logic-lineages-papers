module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleProductComparisonDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def divisibleProductData : Prop :=
  ∀ (R D : Type) [AddCommGroup R] [AddCommGroup D] (p : ℕ) [Fact p.Prime],
    (∀ x : R, ∃ k : ℕ, p^k • x = 0) → (∀ x : D, ∃ k : ℕ, p^k • x = 0) →
    GroupDivisible D →
    (∀ x : R×D, ∃ k : ℕ, p^k • x = 0) ∧
    (∀ (α : Ordinal.{0}) (x : R×D),
      x ∈ transfiniteFiltration p α ↔ x.1 ∈ transfiniteFiltration p α) ∧
    ∀ α : Ordinal.{0},
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup (R×D))) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup R))
/-- The first coordinate itself pays all filtration agreement; there is no BF or rank premise. -/
def divisibleProductComparison : Prop :=
  ∀ (R D E : Type) [AddCommGroup R] [AddCommGroup D] [AddCommGroup E]
    [Countable R] [Countable D] [Countable E] (p : ℕ) [Fact p.Prime],
    (∀ x : R, ∃ k : ℕ, p^k • x = 0) → (∀ x : D, ∃ k : ℕ, p^k • x = 0) →
    (∀ x : E, ∃ k : ℕ, p^k • x = 0) → IsReducedAddGroup R →
    GroupDivisible D → GroupDivisible E →
    ∀ γ : Ordinal.{0}, StagesNonzeroBelow p R (Ordinal.omega0*γ) →
    ∀ (B : AddSubgroup (R×D)) (C : AddSubgroup (R×E)) [Finite B] (f : B ≃+ C),
      (∀ x : B, (f x : R×E).1 = (x:R×D).1) →
      SubgroupComparison f (2*γ)
end LogicLineages.ModelsAlgebra.PGroups.Targets
