module
public import LogicLineages.PermittedControl.RelativeDescentDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Supporting actual top-visit-or-divergence bridge for thick-block admission.
Actual visits, their norm orbits and shared-clock resets are derived, not supplied.
The equal-head case rho=sigma includes an already-admitted top at event zero. -/
def SynchronizedTargetVisits : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu nu sigma rho : Ordinal.{0}) (t : Nat),
  mu < epsilonZero → nu < epsilonZero → sigma < epsilonZero → rho < epsilonZero →
  (mu=0 ∨ Order.IsSuccLimit mu) → (nu=0 ∨ Order.IsSuccLimit nu) →
  Order.IsSuccLimit sigma → Order.IsSuccLimit rho → rho ≤ sigma →
  max 2 (max (actualOrdinalNorm (mu+sigma))
    (max (actualOrdinalNorm (nu+sigma))
      (max (actualOrdinalNorm (mu+rho)) (actualOrdinalNorm (nu+rho))))) ≤ t →
  ∃ i j : Nat,
    FirstEntry f (countInitial (mu+sigma) t) (mu+rho) i ∧
    FirstEntry f (countInitial (nu+sigma) t) (nu+rho) j ∧
    entryNormAt f (countInitial (mu+sigma) t) i = f^[i] t ∧
    entryNormAt f (countInitial (nu+sigma) t) j = f^[j] t ∧
    (∀ h : Nat, h ≤ i → rho ≤ actualLimitPart (relativeState f (mu+sigma) mu t h) ∧
      (actualLimitPart (relativeState f (mu+sigma) mu t h) = rho ↔ h=i)) ∧
    (∀ h : Nat, h ≤ j → rho ≤ actualLimitPart (relativeState f (nu+sigma) nu t h) ∧
      (actualLimitPart (relativeState f (nu+sigma) nu t h) = rho ↔ h=j)) ∧
    (i=j →
      (descentWith f)^[i] (countInitial (mu+sigma) t) = countInitial (mu+rho) (f^[i] t) ∧
      (descentWith f)^[i] (countInitial (nu+sigma) t) = countInitial (nu+rho) (f^[i] t)) ∧
    (i≠j → ∃ h : Nat, h=min i j ∧
      actualLimitPart (relativeState f (mu+sigma) mu t h) ≠
        actualLimitPart (relativeState f (nu+sigma) nu t h) ∧
      rho ≤ actualLimitPart (relativeState f (mu+sigma) mu t h) ∧
      rho ≤ actualLimitPart (relativeState f (nu+sigma) nu t h))

end LogicLineages.PermittedControl.Targets
