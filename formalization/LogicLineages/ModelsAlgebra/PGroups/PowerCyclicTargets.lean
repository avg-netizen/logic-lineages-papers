module

public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclicDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.FiniteImageTableDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupPowerCyclicInclusionEvaluation : Prop :=
  ∀ (p ℓ k : ℕ) (h : ℓ ≤ k) (z : ℤ),
    powerCyclicInclusion p ℓ k h (z : ZMod (p ^ ℓ)) =
      p ^ (k - ℓ) • (z : ZMod (p ^ k))

def groupPowerCyclicInclusionInjective : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ℓ k : ℕ) (h : ℓ ≤ k),
    Function.Injective (powerCyclicInclusion p ℓ k h)

def groupPowerCyclicInclusionRange : Prop :=
  ∀ (p ℓ k : ℕ) (h : ℓ ≤ k),
    (powerCyclicInclusion p ℓ k h).range = multipleImage (ZMod (p ^ k)) (p ^ (k - ℓ))

def groupPowerCyclicSocleRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 0 < k →
    ∀ z : ZMod (p ^ k), p • z = 0 → ∃ y : ZMod (p ^ k), p ^ (k - 1) • y = z

/-- The actual source socle witness; 1 is not p-annihilated when ℓ>1. -/
def groupPowerCyclicSocleWitness : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ), 0 < ℓ →
    p • ((p ^ (ℓ - 1) : ℕ) : ZMod (p ^ ℓ)) = 0 ∧ ((p ^ (ℓ - 1) : ℕ) : ZMod (p ^ ℓ)) ≠ 0

def groupPowerCyclicAnnihilation : Prop :=
  ∀ (p ℓ n : ℕ), ℓ ≤ n → ∀ x : ZMod (p ^ ℓ), p ^ n • x = 0

end LogicLineages.ModelsAlgebra.PGroups.Targets
