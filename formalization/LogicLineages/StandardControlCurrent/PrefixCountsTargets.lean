module
public import LogicLineages.OrdinalComparison.PrefixTraceDefinitions
public import LogicLineages.OrdinalComparison.ActualTerminalDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PrefixCountsTargets
open OrdinalComparison

def ActualCompatiblePrefixMaximum : Prop :=
  ∀ k r : Ordinal.{0}, k < epsilonZero → r < epsilonZero → Order.IsSuccLimit r →
    actualCNFPrefixCompatible k r → ∀ b : Nat, actualOrdinalNorm k ≤ b →
      actualMaximumPredecessor (k + r) b =
        k + actualMaximumPredecessor r (b - actualOrdinalNorm k)

def CompensatedPrefixControlBounds : Prop :=
  ∀ c : Nat, Monotone (compensatedPrefixControl c) ∧
    ∀ n : Nat, Phi n ≤ compensatedPrefixControl c n ∧ n < compensatedPrefixControl c n

def ActualCompatiblePrefixFirstFiniteCut : Prop :=
  ∀ k r : Ordinal.{0}, k < epsilonZero → r < epsilonZero → Order.IsSuccLimit r →
    actualCNFPrefixCompatible k r →
      let g := compensatedPrefixControl (actualOrdinalNorm k)
      let C := actualControlledCount g r
      0 < C ∧
        (∀ i : Nat, i ≤ C → actualControlledStateAfter Phi (k + r) i = k + actualControlledStateAfter g r i) ∧
        (∃ n : Nat, actualControlledStateAfter Phi (k + r) C = k + (n : Ordinal)) ∧
        ∀ i : Nat, i < C → k + Ordinal.omega0 ≤ actualControlledStateAfter Phi (k + r) i

def ActualControlledCountRecursion : Prop :=
  ∀ g : Nat → Nat, ∀ a : Ordinal.{0}, a < epsilonZero →
    (a < Ordinal.omega0 → actualControlledCount g a = 0) ∧
      (Ordinal.omega0 ≤ a →
        actualControlledCount g a = actualControlledCount g (actualControlledStep g a) + 1)

def ActualControlledCountPhiAgreement : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → actualControlledCount Phi a = actualReplacementCount a

def ActualControlledCountsJointMonotone : Prop :=
  ∀ g h : Nat → Nat, (∀ n : Nat, g n ≤ h n) → Monotone h →
    ∀ a a' : Ordinal.{0}, a ≤ a' → a' < epsilonZero →
      actualOrdinalNorm a ≤ actualOrdinalNorm a' →
      actualControlledCount g a ≤ actualControlledCount h a'

def ActualOrderedControlsAndCounts : Prop :=
  ∀ g h : Nat → Nat, Monotone g → Monotone h →
    (∀ n : Nat, n < g n) → (∀ n : Nat, n < h n) → (∀ n : Nat, g n ≤ h n) →
    ∀ a a' : Ordinal.{0}, a ≤ a' → a' < epsilonZero →
      actualOrdinalNorm a ≤ actualOrdinalNorm a' →
      actualControlledCount g a ≤ actualControlledCount h a'

def FullPrefix : Prop := ActualCompatiblePrefixMaximum ∧ CompensatedPrefixControlBounds ∧
  ActualCompatiblePrefixFirstFiniteCut

def FullCounts : Prop := ActualControlledCountRecursion ∧ ActualControlledCountPhiAgreement ∧
  ActualControlledCountsJointMonotone ∧ ActualOrderedControlsAndCounts

end LogicLineages.StandardControlCurrent.PrefixCountsTargets
