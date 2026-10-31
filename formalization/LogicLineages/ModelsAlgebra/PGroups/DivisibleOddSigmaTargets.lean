module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleOddSigmaDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def divisibleProductOddNoSigma : Prop :=
  ∀ (R D : Type) [AddCommGroup R] [AddCommGroup D] [Countable R] [Countable D]
    (p : ℕ) [Fact p.Prime],
    (∀ x : R, ∃ k : ℕ, p^k • x = 0) → (∀ x : D, ∃ k : ℕ, p^k • x = 0) →
    IsReducedAddGroup R → GroupDivisible D →
    ∀ γ : Ordinal.{0}, 0<γ → StagesNonzeroBelow p R (Ordinal.omega0*γ) →
    ∀ φ : Formula 0, Complexity .sigma (2*γ+1) φ → ¬ GroupScottSentence (R×D) φ
def divisibleProductOddNoRawSigma : Prop :=
  ∀ (R D : Type) [AddCommGroup R] [AddCommGroup D] [Countable R] [Countable D]
    (p : ℕ) [Fact p.Prime],
    (∀ x : R, ∃ k : ℕ, p^k • x = 0) → (∀ x : D, ∃ k : ℕ, p^k • x = 0) →
    IsReducedAddGroup R → GroupDivisible D →
    ∀ γ : Ordinal.{0}, 0<γ → StagesNonzeroBelow p R (Ordinal.omega0*γ) →
    ∀ φ : Formula 0, Complexity .sigma (2*γ+1) φ → ¬ RawScottSentence (RawGroupStructure.ofGroup (R×D)) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
