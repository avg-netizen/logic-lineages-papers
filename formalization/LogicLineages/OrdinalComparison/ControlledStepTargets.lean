module
public import LogicLineages.OrdinalComparison.ControlledStepDefinitions

@[expose] public section

/-! Direct source step suppliers for paper07 lem:counts (paper.tex384–407).
They concern the original actual norm-maximal descent with arbitrary controls.
The maximum/saturation facts, control order and monotonicity are not encoded
as fields in the step implementation. Full count monotonicity stays separate. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualControlledStepStrict : Prop :=
  ∀ g : Nat → Nat, ∀ a : Ordinal.{0}, Ordinal.omega0 ≤ a → a < epsilonZero →
    actualControlledStep g a < a

def ActualControlledStepNorm : Prop :=
  ∀ g : Nat → Nat, ∀ a : Ordinal.{0}, Ordinal.omega0 ≤ a → a < epsilonZero →
    actualOrdinalNorm (actualControlledStep g a) = g (actualOrdinalNorm a)

def ActualControlledStepsJointMonotone : Prop :=
  ∀ g h : Nat → Nat, (∀ n : Nat, g n ≤ h n) → Monotone h →
    ∀ a a' : Ordinal.{0}, Ordinal.omega0 ≤ a → a ≤ a' → a' < epsilonZero →
      actualOrdinalNorm a ≤ actualOrdinalNorm a' →
      actualControlledStep g a ≤ actualControlledStep h a' ∧
        actualOrdinalNorm (actualControlledStep g a) ≤ actualOrdinalNorm (actualControlledStep h a')

end LogicLineages.OrdinalComparison.Targets
