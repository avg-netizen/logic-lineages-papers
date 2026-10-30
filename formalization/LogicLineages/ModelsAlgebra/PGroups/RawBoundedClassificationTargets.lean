module
public import LogicLineages.ModelsAlgebra.PGroups.SourceTwoInfiniteTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

/-- Exhaustive actual Ulm patterns and explicit unrestricted Scott bounds.
No decomposition, rank correctness or exact-complexity oracle is a premise. -/
def groupRawBoundedClassification : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] [Infinite G] (N : ℕ),
    (∀ x : G, p^N • x = 0) →
    (∃ a b : Fin N, a < b ∧
        Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val : AddSubgroup G)) = Cardinal.aleph0 ∧
        Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b.val : AddSubgroup G)) = Cardinal.aleph0 ∧
        (∃ φ : Formula 0, Complexity .pi (3 : Ordinal.{0}) φ ∧ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∧
        (∀ φ : Formula 0, Complexity .sigma (3 : Ordinal.{0}) φ → ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∧
        (∀ d : DifferenceFormula 0, d.AtLevel (2 : Ordinal.{0}) → ¬ RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d)) ∨
    (∃ k : ℕ, 0 < k ∧ k ≤ N ∧
        Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) : AddSubgroup G)) = Cardinal.aleph0 ∧
        (∀ j : ℕ, j < N → j ≠ k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0) ∧
        (∃ j : ℕ, j < k-1 ∧ Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) ≠ 0) ∧
        (∃ d : DifferenceFormula 0, d.AtLevel (2 : Ordinal.{0}) ∧ RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d) ∧
        (∀ φ : Formula 0, Complexity .sigma (2 : Ordinal.{0}) φ → ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∧
        (∀ φ : Formula 0, Complexity .pi (2 : Ordinal.{0}) φ → ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ)) ∨
    (∃ k : ℕ, 0 < k ∧ k ≤ N ∧
        Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) : AddSubgroup G)) = Cardinal.aleph0 ∧
        (∀ j : ℕ, j < N → j ≠ k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0) ∧
        (∀ j : ℕ, j < k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) = 0) ∧
        (∃ φ : Formula 0, Complexity .pi (2 : Ordinal.{0}) φ ∧ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∧
        (∀ φ : Formula 0, Complexity .sigma (2 : Ordinal.{0}) φ → ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∧
        (∀ φ : Formula 0, Complexity .pi (1 : Ordinal.{0}) φ → ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∧
        (∀ d : DifferenceFormula 0, d.AtLevel (1 : Ordinal.{0}) → ¬ RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d))

end LogicLineages.ModelsAlgebra.PGroups.Targets
