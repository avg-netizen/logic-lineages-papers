module
public import LogicLineages.PermittedControl.RelativeDescentDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Actual maximum, including its own membership, reconstruction and comparison
against all eligible relative candidates. No greatest-element oracle premise. -/
def RelativeMaximumSpec : Prop := ∀ (mu rho : Ordinal.{0}) (b : Nat),
  mu + rho < epsilonZero → 0 < rho → actualOrdinalNorm mu ≤ b →
  actualMaximumPredecessor (mu + rho) b = mu + relativeMaximum mu rho b ∧
  IsGreatest {y : Ordinal.{0} | y < rho ∧ actualOrdinalNorm y + relativeCost mu y ≤ b}
    (relativeMaximum mu rho b)

/-- Generic one-step conjugacy. Next budget is the actual control applied to
N(mu+y), not an independently supplied numerical orbit. -/
def RelativeDescentStep : Prop := ∀ (f : Nat → Nat) (mu y : Ordinal.{0}),
  mu + y < epsilonZero → (mu = 0 ∨ Order.IsSuccLimit mu) → Ordinal.omega0 ≤ y →
  actualOrdinalNorm mu ≤ f (actualOrdinalNorm (mu+y)) →
  actualLimitPart (mu+y) = mu + actualLimitPart y ∧
  descentWith f (mu+y) = mu +
    relativeMaximum mu (actualLimitPart y) (f (actualOrdinalNorm (mu+y)))

/-- Complete source relative recursion along a genuine affordable selected-control
entry. Existence, first-finite equivalence, actual orbit budgets and initial gap
are all proved together; neither a relative recursion nor a successful hit is
supplied as a hypothesis. -/
def RelativeEntryRecursion : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lam mu delta : Ordinal.{0}) (t : Nat), lam < epsilonZero →
  Order.IsSuccLimit lam → (mu = 0 ∨ Order.IsSuccLimit mu) → mu < lam →
  Order.IsSuccLimit delta → mu + delta = lam →
  max 2 (max (actualOrdinalNorm lam) (actualOrdinalNorm mu)) ≤ t →
  ∃ tau : Nat, FirstEntry f (countInitial lam t) mu tau ∧
    relativeState f lam mu t 0 = delta + ((t-actualOrdinalNorm lam : Nat) : Ordinal) ∧
    (∀ i : Nat, i ≤ tau →
      (descentWith f)^[i] (countInitial lam t) = mu + relativeState f lam mu t i ∧
      actualOrdinalNorm ((descentWith f)^[i] (countInitial lam t)) = f^[i] t ∧
      actualOrdinalNorm (relativeState f lam mu t i) ≤ f^[i] t ∧
      (relativeState f lam mu t i < Ordinal.omega0 ↔ i = tau)) ∧
    (∀ i : Nat, i < tau →
      relativeState f lam mu t (i+1) =
        relativeMaximum mu (actualLimitPart (relativeState f lam mu t i)) (f^[i+1] t))

end LogicLineages.PermittedControl.Targets
