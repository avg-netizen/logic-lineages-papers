module
public import LogicLineages.OrdinalComparison.PrefixTraceTargets
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullFixedBudget.Targets
open LogicLineages.OrdinalComparison

def NumericalCount : Prop :=
  ∀ d c S n : Nat, 1 ≤ d → c + d + 1 ≤ S →
    c + actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)) ≤ S →
      actualControlledCount (fun _ => S - c)
        (Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)) = restrictedPartitionCount d (S - c)

def RetainedPrefixCount : Prop :=
  ∀ k : Ordinal.{0}, k < epsilonZero → ∀ d S n : Nat, 1 ≤ d →
    actualMinExponentAtLeast k (d : Ordinal) → actualOrdinalNorm k + d + 1 ≤ S →
    actualOrdinalNorm k + actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)) ≤ S →
      let r := Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)
      let C := restrictedPartitionCount d (S - actualOrdinalNorm k)
      0 < C ∧
        (∀ i : Nat, i ≤ C → actualControlledStateAfter (fun _ => S) (k + r) i =
          k + actualControlledStateAfter (fun _ => S - actualOrdinalNorm k) r i) ∧
        (∃ t : Nat, actualControlledStateAfter (fun _ => S) (k + r) C = k + (t : Ordinal)) ∧
        ∀ i : Nat, i < C → k + Ordinal.omega0 ≤ actualControlledStateAfter (fun _ => S) (k + r) i

def CompleteFixedBudget : Prop := NumericalCount ∧ RetainedPrefixCount
end LogicLineages.CartierObserverCurrent.FullFixedBudget.Targets
