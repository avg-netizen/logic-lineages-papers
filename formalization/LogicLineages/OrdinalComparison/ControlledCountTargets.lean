module
public import LogicLineages.OrdinalComparison.ControlledCountDefinitions
public import LogicLineages.OrdinalComparison.ActualTerminalDefinitions

@[expose] public section

/-! Independent full source paper07 lem:counts comparator. Arbitrary actual
controls retain the original increasing/exceeds-input assumptions. A stronger
joint monotonicity supplier and fixed-Phi correspondence are explicit gates;
no count law, termination or identification with the source is a premise. -/

namespace LogicLineages.OrdinalComparison.Targets

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

def FullActualOrderedControlsAndCounts : Prop :=
  ActualControlledCountRecursion ∧ ActualControlledCountPhiAgreement ∧
    ActualControlledCountsJointMonotone ∧ ActualOrderedControlsAndCounts

end LogicLineages.OrdinalComparison.Targets
