module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedOddSigmaDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def reducedOddNoSigma : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x:G, ∃ k:ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ γ : Ordinal.{0}, 0<γ → StagesNonzeroBelow p G (Ordinal.omega0*γ) →
    ∀ φ : Formula 0, Complexity .sigma (2*γ+1) φ → ¬ GroupScottSentence G φ
def reducedOddNoRawSigma : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x:G, ∃ k:ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ γ : Ordinal.{0}, 0<γ → StagesNonzeroBelow p G (Ordinal.omega0*γ) →
    ∀ φ : Formula 0, Complexity .sigma (2*γ+1) φ →
      ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
