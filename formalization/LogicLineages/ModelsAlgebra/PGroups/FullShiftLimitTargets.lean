module

public import LogicLineages.ModelsAlgebra.PGroups.FullShiftDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.EndomorphismLimitDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.ScottDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe v

def groupFullShiftLimitSocleRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ) (h : ∀ j, ℓ j ≤ k)
    (s : ℕ) (r : Fin s → ℕ), 0 < k → (∀ a, k ≤ r a) →
      ∀ z : EndomorphismLimit (fullShiftHom p k t ℓ h s r), p • z = 0 →
        ∃ y : EndomorphismLimit (fullShiftHom p k t ℓ h s r), p ^ (k - 1) • y = z

def groupFullShiftLimitNotIsomorphic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ) (h : ∀ j, ℓ j ≤ k)
    (s : ℕ) (r : Fin s → ℕ), 0 < k → (∀ a, k ≤ r a) →
      ∀ j : Fin t, 0 < ℓ j → ℓ j < k →
        ¬ Nonempty (FullShiftGroup p k t ℓ s r ≃+ EndomorphismLimit (fullShiftHom p k t ℓ h s r))

def groupFullShiftNoPiTwoScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ) (h : ∀ j, ℓ j ≤ k)
    (s : ℕ) (r : Fin s → ℕ), 0 < k → (∀ a, k ≤ r a) →
      ∀ j : Fin t, 0 < ℓ j → ℓ j < k → ∀ φ : Formula 0,
        Complexity .pi (2 : Ordinal.{v}) φ → ¬ GroupScottSentence (FullShiftGroup p k t ℓ s r) φ

/-- Exact displayed finite-short/strict-upper normal forms from paper01.
No cyclic-decomposition existence theorem for an arbitrary group is asserted. -/
def groupSourceFiniteBlocksNoPiTwoScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ) (s : ℕ) (r : Fin s → ℕ),
    0 < t → (∀ j, 0 < ℓ j ∧ ℓ j < k) → (∀ a, k < r a) → ∀ φ : Formula 0,
      Complexity .pi (2 : Ordinal.{v}) φ → ¬ GroupScottSentence (FullShiftGroup p k t ℓ s r) φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
