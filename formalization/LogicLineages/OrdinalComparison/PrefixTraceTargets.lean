module
public import LogicLineages.OrdinalComparison.PrefixTraceDefinitions
public import LogicLineages.OrdinalComparison.CompatiblePrefixTargets
public import LogicLineages.OrdinalComparison.ConstantBudgetTargets

@[expose] public section

/-! Full actual source trace contracts for paper07 lem:prefix and paper10
lem:fixed. A relative first-finite cut stops at prefix+n and is kept distinct
from the global collapse terminal count. The count, all trace equations and
absence of an earlier cut are conclusions, not new implementation fields. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualControlledTraceFirstFinite : Prop :=
  ∀ g : Nat → Nat, ∀ a : Ordinal.{0}, a < epsilonZero →
    actualControlledStateAfter g a (actualControlledCount g a) < Ordinal.omega0 ∧
      ∀ i : Nat, i ≤ actualControlledCount g a →
        actualControlledStateAfter g a i < epsilonZero ∧
        actualControlledStateAfter g a i ≤ a ∧
        (i < actualControlledCount g a → Ordinal.omega0 ≤ actualControlledStateAfter g a i)

def ActualLimitPartPrefixAddition : Prop :=
  ∀ k : Ordinal.{0}, Ordinal.omega0 ∣ k → ∀ r : Ordinal.{0},
    actualLimitPart (k + r) = k + actualLimitPart r

def ActualPrefixControlStep : Prop :=
  ∀ h : Nat → Nat, ∀ k r : Ordinal.{0}, k < epsilonZero → r < epsilonZero →
    Ordinal.omega0 ≤ r → ∀ e : Ordinal.{0}, 0 < e → actualMinExponentAtLeast k e →
      r < Ordinal.omega0 ^ (e + 1) →
      actualOrdinalNorm k ≤ h (actualOrdinalNorm k + actualOrdinalNorm r) →
        actualControlledStep h (k + r) =
          k + actualControlledStep (prefixRemainderControl h (actualOrdinalNorm k)) r

def ActualPrefixControlTrace : Prop :=
  ∀ h : Nat → Nat, ∀ k r : Ordinal.{0}, k < epsilonZero → r < epsilonZero →
    ∀ e : Ordinal.{0}, 0 < e → actualMinExponentAtLeast k e → r < Ordinal.omega0 ^ (e + 1) →
      (∀ n : Nat, actualOrdinalNorm k ≤ h (actualOrdinalNorm k + n)) →
      let g := prefixRemainderControl h (actualOrdinalNorm k)
      let C := actualControlledCount g r
      (∀ i : Nat, i ≤ C → actualControlledStateAfter h (k + r) i = k + actualControlledStateAfter g r i) ∧
        actualControlledStateAfter g r C < Ordinal.omega0 ∧
        ∀ i : Nat, i < C → k + Ordinal.omega0 ≤ actualControlledStateAfter h (k + r) i

def ActualCompatiblePrefixFirstFiniteCut : Prop :=
  ∀ k r : Ordinal.{0}, k < epsilonZero → r < epsilonZero → Order.IsSuccLimit r →
    actualCNFPrefixCompatible k r →
      let g := compensatedPrefixControl (actualOrdinalNorm k)
      let C := actualControlledCount g r
      0 < C ∧
        (∀ i : Nat, i ≤ C → actualControlledStateAfter Phi (k + r) i = k + actualControlledStateAfter g r i) ∧
        (∃ n : Nat, actualControlledStateAfter Phi (k + r) C = k + (n : Ordinal)) ∧
        ∀ i : Nat, i < C → k + Ordinal.omega0 ≤ actualControlledStateAfter Phi (k + r) i

def ActualRetainedPrefixFixedBudgetCount : Prop :=
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

def FullActualCompatiblePrefixSplitting : Prop :=
  ActualCompatiblePrefixMaximum ∧ CompensatedPrefixControlBounds ∧ ActualCompatiblePrefixFirstFiniteCut

def FullActualFixedBudgetPartitionCount : Prop :=
  ActualNumericalFixedBudgetPartitionCount ∧ ActualRetainedPrefixFixedBudgetCount

end LogicLineages.OrdinalComparison.Targets
