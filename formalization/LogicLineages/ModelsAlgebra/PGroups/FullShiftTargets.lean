module

public import LogicLineages.ModelsAlgebra.PGroups.FullShiftDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupFullShiftInjective : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ) (h : ∀ j, ℓ j ≤ k)
    (s : ℕ) (r : Fin s → ℕ), Function.Injective (fullShiftHom p k t ℓ h s r)

def groupFullShiftSocleRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ) (h : ∀ j, ℓ j ≤ k)
    (s : ℕ) (r : Fin s → ℕ), 0 < k → (∀ a, k ≤ r a) →
      ∀ x : FullShiftGroup p k t ℓ s r, p • x = 0 →
        ∃ y : FullShiftGroup p k t ℓ s r,
          p ^ (k - 1) • y = fullShiftHom p k t ℓ h s r x

def groupFullShortNoRoot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ) (s : ℕ) (r : Fin s → ℕ) (j : Fin t),
    0 < ℓ j → ℓ j < k → p • fullShortWitness p k t ℓ s r j = 0 ∧
      ¬ ∃ y : FullShiftGroup p k t ℓ s r, p ^ (k - 1) • y = fullShortWitness p k t ℓ s r j

/-- Actual computed exponent bound: no upper-bound oracle is supplied. -/
def groupFullShiftExponent : Prop :=
  ∀ (p k t : ℕ) (ℓ : Fin t → ℕ), (∀ j, ℓ j ≤ k) →
    ∀ (s : ℕ) (r : Fin s → ℕ) (x : FullShiftGroup p k t ℓ s r),
      p ^ fullExponentBound k s r • x = 0

def groupFullShiftCountable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ) (s : ℕ) (r : Fin s → ℕ),
    Countable (FullShiftGroup p k t ℓ s r)

def groupFullShiftInfinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ) (s : ℕ) (r : Fin s → ℕ),
    0 < k → Infinite (FullShiftGroup p k t ℓ s r)

end LogicLineages.ModelsAlgebra.PGroups.Targets
