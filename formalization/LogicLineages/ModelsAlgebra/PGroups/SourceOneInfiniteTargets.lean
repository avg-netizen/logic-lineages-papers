module
public import LogicLineages.ModelsAlgebra.PGroups.OneInfiniteBoundsTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

/-- The actual unique-infinite Ulm-rank pattern, positive-lower source subcase. -/
def groupSourcePositiveLowerScottBounds : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (k N : ℕ),
    0 < k → k ≤ N → (∀ g : G, p ^ N • g = 0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) : AddSubgroup G)) = Cardinal.aleph0 →
    (∀ j : ℕ, j < N → j ≠ k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0) →
    (∃ j : ℕ, j < k-1 ∧ Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) ≠ 0) →
    (∃ d : DifferenceFormula 0, d.AtLevel (2 : Ordinal.{0}) ∧ DifferenceScottSentence G d) ∧
    (∀ φ : Formula 0, Complexity .sigma (2 : Ordinal.{0}) φ → ¬ GroupScottSentence G φ) ∧
    (∀ φ : Formula 0, Complexity .pi (2 : Ordinal.{0}) φ → ¬ GroupScottSentence G φ)

/-- The actual unique-infinite Ulm-rank pattern, zero-lower source subcase. -/
def groupSourceZeroLowerScottBounds : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (k N : ℕ),
    0 < k → k ≤ N → (∀ g : G, p ^ N • g = 0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) : AddSubgroup G)) = Cardinal.aleph0 →
    (∀ j : ℕ, j < N → j ≠ k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0) →
    (∀ j : ℕ, j < k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) = 0) →
    (∃ φ : Formula 0, Complexity .pi (2 : Ordinal.{0}) φ ∧ GroupScottSentence G φ) ∧
    (∀ φ : Formula 0, Complexity .pi (1 : Ordinal.{0}) φ → ¬ GroupScottSentence G φ) ∧
    (∀ d : DifferenceFormula 0, d.AtLevel (1 : Ordinal.{0}) → ¬ DifferenceScottSentence G d)

end LogicLineages.ModelsAlgebra.PGroups.Targets
