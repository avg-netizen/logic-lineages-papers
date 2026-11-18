module
public import LogicLineages.OrdinalComparison.GrowingBudgetTransferTargets
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullBudgetTransfer.Targets
open LogicLineages.OrdinalComparison

def NumericalTransfer : Prop :=
  ∀ d m c S n : Nat, 1 ≤ d → 1 ≤ m → c ≤ S → ∀ h : Nat → Nat,
    let g := fun i => h i - c
    let a := Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)
    (∀ i : Nat, i < actualScheduledCount g a →
      let u := c + actualOrdinalNorm (actualScheduledStateAfter g a i)
      u ≤ h i ∧ Nat.ModEq (restrictedPartitionPeriod d m) (h i) S) →
    Nat.ModEq m (actualScheduledCount g a) (restrictedPartitionCount d (S - c))

def PrefixTransfer : Prop :=
  ∀ d m : Nat, 1 ≤ d → 1 ≤ m → ∀ k : Ordinal.{0}, k < epsilonZero →
    actualMinExponentAtLeast k (d : Ordinal) → ∀ S n : Nat, actualOrdinalNorm k ≤ S →
    ∀ h : Nat → Nat,
      let c := actualOrdinalNorm k
      let g := fun i => h i - c
      let a := Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)
      let C := actualScheduledCount g a
      (∀ i : Nat, i < C →
        let u := c + actualOrdinalNorm (actualScheduledStateAfter g a i)
        u ≤ h i ∧ Nat.ModEq (restrictedPartitionPeriod d m) (h i) S) →
      Nat.ModEq m C (restrictedPartitionCount d (S - c)) ∧
        (∀ i : Nat, i ≤ C → actualScheduledStateAfter h (k + a) i =
          k + actualScheduledStateAfter g a i) ∧
        (∃ t : Nat, actualScheduledStateAfter h (k + a) C = k + (t : Ordinal)) ∧
        ∀ i : Nat, i < C → k + Ordinal.omega0 ≤ actualScheduledStateAfter h (k + a) i

def CompleteTransfer : Prop :=
  LogicLineages.OrdinalComparison.Targets.ActualScheduledFirstFinite ∧
    NumericalTransfer ∧ PrefixTransfer
end LogicLineages.CartierObserverCurrent.FullBudgetTransfer.Targets
