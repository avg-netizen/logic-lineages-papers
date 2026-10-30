module
public import LogicLineages.OrdinalComparison.CartierOrbitTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Entire source paper10 thm:actual-period (lines597–642). State equality
is equality of genuine rational differentials, not of an opaque observation.
A single coincidence already forces divisibility, hence in particular every
eventual period does. No finite-tail existence or transport oracle is assumed. -/
def ActualCompleteCartierPeriodDivisibility : Prop :=
  ∀ u : Nat, 5 ≤ u → ∀ j p : Nat,
    (actualDifferentialCartier (K := ActualResidueField))^[j + p] (actualLinkedDifferential u) =
      (actualDifferentialCartier (K := ActualResidueField))^[j] (actualLinkedDifferential u) →
    2 * actualLinkedHalfExponent u ∣ p

def FullActualSourceCartierPeriod : Prop :=
  ∀ v : Nat, 4 ≤ v →
    Function.minimalPeriod (actualResidueTupleFrobenius (Phi v)) (actualResidueTuple (Phi v)) =
      2 * (Nat.log 2 (actualLinkedBudget (Phi v)) - 1) ∧
    ∀ j p : Nat,
      (actualDifferentialCartier (K := ActualResidueField))^[j + p] (actualLinkedDifferential (Phi v)) =
        (actualDifferentialCartier (K := ActualResidueField))^[j] (actualLinkedDifferential (Phi v)) →
      2 * (Nat.log 2 (actualLinkedBudget (Phi v)) - 1) ∣ p

end LogicLineages.OrdinalComparison.Targets
