module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleCompetitorDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth
/-- Every actual finite tuple has a genuine nonisomorphic primary competitor.
No finite-rank, quotient, parameter-retention, or comparison oracle is an input. -/
def divisibleProductCompetitor : Prop :=
  ∀ (R D : Type) [AddCommGroup R] [AddCommGroup D] [Countable R] [Countable D]
    (p : ℕ) [Fact p.Prime],
    (∀ x : R, ∃ k : ℕ, p^k • x = 0) → (∀ x : D, ∃ k : ℕ, p^k • x = 0) →
    IsReducedAddGroup R → GroupDivisible D →
    ∀ γ : Ordinal.{0}, StagesNonzeroBelow p R (Ordinal.omega0*γ) →
    ∀ (n : ℕ) (a : Fin n → R×D),
      ∃ (H : Type) (inst : AddCommGroup H), letI := inst; Countable H ∧
        (∀ x : H, ∃ k : ℕ, p^k • x = 0) ∧
        ¬ Nonempty ((R×D) ≃+ H) ∧
        ∃ b : Fin n → H, BackAndForth (2*γ) a b
end LogicLineages.ModelsAlgebra.PGroups.Targets
