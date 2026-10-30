module
public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicLowerTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

/-- Explicit relative upper/lower bounds for the positive-lower source subcase. -/
def groupPositiveLowerScottBounds : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (k N : ℕ),
    0 < k → k ≤ N → (∀ g : G, p ^ N • g = 0) →
    Finite (multipleImage G (p ^ k)) → Infinite (multipleImage G (p ^ (k-1))) →
    (∀ j : ℕ, j < k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0) →
    (∃ j : ℕ, j < k-1 ∧ Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) ≠ 0) →
    (∃ d : DifferenceFormula 0, d.AtLevel (2 : Ordinal.{0}) ∧ DifferenceScottSentence G d) ∧
    (∀ φ : Formula 0, Complexity .sigma (2 : Ordinal.{0}) φ → ¬ GroupScottSentence G φ) ∧
    (∀ φ : Formula 0, Complexity .pi (2 : Ordinal.{0}) φ → ¬ GroupScottSentence G φ)

/-- Explicit relative upper/lower bounds for the zero-lower source subcase. -/
def groupZeroLowerScottBounds : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (k N : ℕ),
    0 < k → k ≤ N → (∀ g : G, p ^ N • g = 0) →
    Finite (multipleImage G (p ^ k)) → Infinite (multipleImage G (p ^ (k-1))) →
    (∀ j : ℕ, j < k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) = 0) →
    (∃ φ : Formula 0, Complexity .pi (2 : Ordinal.{0}) φ ∧ GroupScottSentence G φ) ∧
    (∀ φ : Formula 0, Complexity .pi (1 : Ordinal.{0}) φ → ¬ GroupScottSentence G φ) ∧
    (∀ d : DifferenceFormula 0, d.AtLevel (1 : Ordinal.{0}) → ¬ DifferenceScottSentence G d)

end LogicLineages.ModelsAlgebra.PGroups.Targets
