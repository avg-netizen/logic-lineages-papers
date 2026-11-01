module
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
/-- Actual unrestricted Sigma_1 exclusion for all countable primary groups,
including finite and divisible groups, rather than reduced groups alone. -/
def primaryNoRawSigmaOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    ∀ φ : Formula 0, Complexity .sigma (1 : Ordinal.{0}) φ →
      ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ
/-- Actual zero-level exclusion in the original language. -/
def primaryNoRawSigmaZero : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    ∀ φ : Formula 0, Complexity .sigma (0 : Ordinal.{0}) φ →
      ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ
/-- A literal Sigma_2 Scott sentence forces finiteness and an actual lower
d-Sigma_1 Scott sentence; no Miller collapse is a hypothesis. -/
def primaryRawSigmaTwoLowering : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G],
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    ∀ φ : Formula 0, Complexity .sigma (2 : Ordinal.{0}) φ →
      RawScottSentence (RawGroupStructure.ofGroup G) φ →
      Finite G ∧ ∃ d : DifferenceFormula 0, d.AtLevel (1 : Ordinal.{0}) ∧
        RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d
end LogicLineages.ModelsAlgebra.PGroups.Targets
