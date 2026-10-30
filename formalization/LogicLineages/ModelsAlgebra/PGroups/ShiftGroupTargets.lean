module

public import LogicLineages.ModelsAlgebra.PGroups.ShiftGroupDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupShiftCoordinates : Prop :=
  ∀ (p : ℕ) (x : ShiftGroup p),
    (shiftHom p x).1 = 0 ∧ (shiftHom p x).2 0 = primeSquareInclusion p x.1 ∧
      ∀ i : ℕ, (shiftHom p x).2 (i + 1) = x.2 i

def groupShiftInjective : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Function.Injective (shiftHom p)

/-- Genuine finite-support root lifting inside the long-summand direct sum. -/
def groupSquareFinsuppSocleRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (v : ℕ →₀ ZMod (p ^ 2)), p • v = 0 →
    ∃ w : ℕ →₀ ZMod (p ^ 2), p • w = v

def groupShiftSocleRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (x : ShiftGroup p), p • x = 0 →
    ∃ y : ShiftGroup p, p • y = shiftHom p x

def groupShiftShortNoRoot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    p • ((1, 0) : ShiftGroup p) = 0 ∧
      ¬ ∃ y : ShiftGroup p, p • y = ((1, 0) : ShiftGroup p)

def groupShiftCountable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Countable (ShiftGroup p)

def groupShiftInfinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Infinite (ShiftGroup p)

end LogicLineages.ModelsAlgebra.PGroups.Targets
