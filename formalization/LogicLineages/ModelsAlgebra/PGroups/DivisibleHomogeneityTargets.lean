module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleHomogeneityDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Actual finite-subgroup ultrahomogeneity of a divisible primary group.
This is a supplier for short-length tuple orbits, not an assumed orbit field. -/
def primaryDivisibleFiniteHomogeneity : Prop :=
  ∀ (D : Type) [AddCommGroup D] [Countable D] (p : ℕ) [Fact p.Prime],
    (∀ x : D, ∃ k : ℕ, p^k • x = 0) → GroupDivisible D →
    ∀ (B C : AddSubgroup D) [Finite B] (f : B ≃+ C),
      ∃ e : D ≃+ D, ∀ x : B, e x = (f x:D)
/-- A genuine endomorphism of a divisible primary group which is a bijection
on its actual p-socle is a bijection on the entire group. -/
def primaryDivisibleSocleDetectsAutomorphism : Prop :=
  ∀ (D : Type) [AddCommGroup D] (p : ℕ) [Fact p.Prime],
    (∀ x : D, ∃ k : ℕ, p^k • x = 0) → GroupDivisible D →
    ∀ f : D →+ D,
      Function.Bijective (socleEndomorphism D p f) →
      Function.Bijective f
end LogicLineages.ModelsAlgebra.PGroups.Targets
