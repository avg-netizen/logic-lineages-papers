module
public import LogicLineages.ModelsAlgebra.PGroups.CountableReducedZeroDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- P-surjectivity implies full divisibility for an actual p-primary group. -/
def pPrimaryDivisibleFromPSurjective : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    (∀ x : G, ∃ y : G, p • y = x) →
    ∀ n : ℕ, n ≠ 0 → ∀ x : G, ∃ y : G, n • y = x
/-- Stabilization at an actually countable ordinal, not merely a large cardinal bound. -/
def countablePFiltrationStabilizes : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ),
    ∃ α : Ordinal.{0}, Countable α.ToType ∧
      (transfiniteFiltration p (α+1) : AddSubgroup G) = transfiniteFiltration p α
/-- Actual countable reduced p-primary groups reach zero at a countable limit cut. -/
def countableReducedZeroLimit : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    (∀ S : AddSubgroup G, (∀ n : ℕ, n ≠ 0 → ∀ x : S, ∃ y : S, n • y = x) → S = ⊥) →
    ∃ δ : Ordinal.{0}, Countable δ.ToType ∧ Order.IsSuccLimit δ ∧
      (transfiniteFiltration p δ : AddSubgroup G) = ⊥
end LogicLineages.ModelsAlgebra.PGroups.Targets
