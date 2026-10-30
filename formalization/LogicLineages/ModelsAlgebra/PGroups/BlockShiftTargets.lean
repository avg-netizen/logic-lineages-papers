module

public import LogicLineages.ModelsAlgebra.PGroups.BlockShiftDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupFiniteBlockCoordinates : Prop :=
  ∀ (p k t : ℕ) (ℓ : Fin t → ℕ) (h : ∀ j, ℓ j ≤ k)
    (a : ∀ j : Fin t, ZMod (p ^ ℓ j)),
      (∀ j : Fin t, finiteBlockInsert p k t ℓ h a j.val = powerCyclicInclusion p (ℓ j) k (h j) (a j)) ∧
      ∀ i : ℕ, finiteBlockInsert p k t ℓ h a (t + i) = 0

def groupBlockShiftCoordinates : Prop :=
  ∀ (p k t : ℕ) (ℓ : Fin t → ℕ) (h : ∀ j, ℓ j ≤ k) (x : BlockShiftGroup p k t ℓ),
    (blockShiftHom p k t ℓ h x).1 = 0 ∧
      (∀ j : Fin t, (blockShiftHom p k t ℓ h x).2 j.val = powerCyclicInclusion p (ℓ j) k (h j) (x.1 j)) ∧
      ∀ i : ℕ, (blockShiftHom p k t ℓ h x).2 (t + i) = x.2 i

def groupBlockShiftInjective : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ) (h : ∀ j, ℓ j ≤ k),
    Function.Injective (blockShiftHom p k t ℓ h)

def groupPowerFinsuppSocleRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 0 < k →
    ∀ v : ℕ →₀ ZMod (p ^ k), p • v = 0 → ∃ w : ℕ →₀ ZMod (p ^ k), p ^ (k - 1) • w = v

/-- Roots of the shifted socle in the actual source group, not the limit. -/
def groupBlockShiftSocleRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ), 0 < k →
    ∀ (ℓ : Fin t → ℕ) (h : ∀ j, ℓ j ≤ k) (x : BlockShiftGroup p k t ℓ), p • x = 0 →
      ∃ y : BlockShiftGroup p k t ℓ, p ^ (k - 1) • y = blockShiftHom p k t ℓ h x

def groupBlockShortNoRoot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ) (j : Fin t),
    0 < ℓ j → ℓ j < k →
      p • blockShortWitness p k t ℓ j = 0 ∧
        ¬ ∃ y : BlockShiftGroup p k t ℓ, p ^ (k - 1) • y = blockShortWitness p k t ℓ j

def groupBlockShiftExponent : Prop :=
  ∀ (p k t : ℕ) (ℓ : Fin t → ℕ), (∀ j, ℓ j ≤ k) →
    ∀ x : BlockShiftGroup p k t ℓ, p ^ k • x = 0

def groupBlockShiftCountable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ), Countable (BlockShiftGroup p k t ℓ)

def groupBlockShiftInfinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k t : ℕ) (ℓ : Fin t → ℕ), 0 < k → Infinite (BlockShiftGroup p k t ℓ)

end LogicLineages.ModelsAlgebra.PGroups.Targets
