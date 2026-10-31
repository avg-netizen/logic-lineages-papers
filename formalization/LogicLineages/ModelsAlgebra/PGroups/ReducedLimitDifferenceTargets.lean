module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLimitDifferenceDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def reducedLimitNoDifference : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x:G, ∃ k:ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ γ : Ordinal.{0}, 0<γ → StagesNonzeroBelow p G (Ordinal.omega0*γ) →
    ∀ d : DifferenceFormula 0, d.AtLevel (2*γ) → ¬ DifferenceScottSentence G d
def reducedLimitNoRawDifference : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x:G, ∃ k:ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ γ : Ordinal.{0}, 0<γ → StagesNonzeroBelow p G (Ordinal.omega0*γ) →
    ∀ d : DifferenceFormula 0, d.AtLevel (2*γ) →
      ¬ RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d
end LogicLineages.ModelsAlgebra.PGroups.Targets
