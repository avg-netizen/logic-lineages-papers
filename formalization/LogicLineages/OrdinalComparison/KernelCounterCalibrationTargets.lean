module

public import LogicLineages.OrdinalComparison.KernelCounterCalibrationDefinitions
public import LogicLineages.OrdinalComparison.ControlledCountDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def KernelPeriodPositive : Prop :=
  ∀ d m : Nat, 1 ≤ d → 1 ≤ m →
    0 < restrictedPartitionPeriod d m ∧
      fastControlResidue (restrictedPartitionPeriod d m) < restrictedPartitionPeriod d m

def KernelModularDifferenceCorrect : Prop :=
  ∀ Q r c : Nat, 0 < Q → r < Q →
    kernelModularDifference Q r c < Q ∧
      ∀ S : Nat, c ≤ S → Nat.ModEq Q S r →
        Nat.ModEq Q (S - c) (kernelModularDifference Q r c)

def PartitionInputCongruence : Prop :=
  ∀ d m : Nat, 1 ≤ d → 1 ≤ m → ∀ a b : Nat,
    Nat.ModEq (restrictedPartitionPeriod d m) a b →
      Nat.ModEq m (restrictedPartitionCount d a) (restrictedPartitionCount d b)

def ActualFiniteKernelInput : Prop :=
  ∀ d c t : Nat, 1 ≤ d → c + d + 1 ≤ t →
    let pi := Ordinal.omega0 ^ (d : Ordinal)
    let I := actualSuffixKernelInitial pi c t
    actualOrdinalNorm pi = d + 1 ∧ I < epsilonZero ∧
      c + actualOrdinalNorm I = t ∧ c ≤ Phi t

def ActualFiniteKernelSchedule : Prop :=
  ∀ d c t : Nat, 1 ≤ d → c + d + 1 ≤ t →
    let pi := Ordinal.omega0 ^ (d : Ordinal)
    let I := actualSuffixKernelInitial pi c t
    let g := compensatedPrefixControl c
    let B := actualControlBudgetStream g I
    let E := actualSuffixKernelCount pi c t
    actualScheduledCount B I = E ∧
      (∀ i : Nat, actualScheduledStateAfter B I i = actualControlledStateAfter g I i) ∧
      (∀ i : Nat, i ≤ E → B i = (Phi^[i + 1]) t - c) ∧
      B 0 = Phi t - c

end LogicLineages.OrdinalComparison.Targets
