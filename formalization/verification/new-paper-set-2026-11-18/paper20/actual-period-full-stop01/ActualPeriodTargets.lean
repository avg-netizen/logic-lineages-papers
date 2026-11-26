module
public import LogicLineages.OrdinalComparison.CartierOrbitDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ActualPeriod.Targets
open LogicLineages.OrdinalComparison

/-- Current20 thm:actual-period. The tuple consists of actual initial Laurent
residues at ALL primitive q-roots in the algebraic closure of F2. -/
def ExactTuplePeriod : Prop := ∀ v : Nat, 4 ≤ v →
  let u := Phi v
  let B := Phi u
  let r := Nat.log 2 B - 1
  Function.minimalPeriod (actualResidueTupleFrobenius u) (actualResidueTuple u) = 2 * r

/-- Genuine whole rational differential equality, not equality of a selected observation.
The single-coincidence form is stronger than the printed eventual-period claim. -/
def ActualStateCoincidence : Prop := ∀ v : Nat, 4 ≤ v →
  let u := Phi v
  let B := Phi u
  let r := Nat.log 2 B - 1
  ∀ j p : Nat,
    (actualDifferentialCartier (K := ActualResidueField))^[j + p] (actualLinkedDifferential u) =
      (actualDifferentialCartier (K := ActualResidueField))^[j] (actualLinkedDifferential u) →
    2 * r ∣ p

/-- Literal eventual-period quantifier, with every future rational state retained. -/
def EventualPeriodDivisibility : Prop := ∀ v : Nat, 4 ≤ v →
  let u := Phi v
  let B := Phi u
  let r := Nat.log 2 B - 1
  ∀ p : Nat, (∃ j : Nat, ∀ k : Nat,
    (actualDifferentialCartier (K := ActualResidueField))^[j + k + p] (actualLinkedDifferential u) =
      (actualDifferentialCartier (K := ActualResidueField))^[j + k] (actualLinkedDifferential u)) →
    2 * r ∣ p

def CompleteActualPeriod : Prop := ExactTuplePeriod ∧ ActualStateCoincidence ∧ EventualPeriodDivisibility
end LogicLineages.CartierObserverCurrent.ActualPeriod.Targets
