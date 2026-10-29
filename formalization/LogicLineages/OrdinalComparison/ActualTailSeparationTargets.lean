module
public import LogicLineages.OrdinalComparison.ActualTerminalDefinitions

@[expose] public section

/-! Independent suppliers and full paper-05 `lem:tail-separation` target.
The count comparison retains BOTH ordinal and norm comparison hypotheses;
there is no asserted global monotonicity of the collapse. All operations on
actual ordinals are ordinary, and the final theorem includes the source's
injectivity conclusion without assuming any supplier as a premise.
-/

namespace LogicLineages.OrdinalComparison.Targets

def ActualLimitPartMonotone : Prop := Monotone actualLimitPart

def ActualMaximumJointMonotone : Prop :=
  ∀ a a' : Ordinal.{0}, 0 < a → a ≤ a' → a' < epsilonZero →
    ∀ b b' : Nat, b ≤ b' → actualMaximumPredecessor a b ≤ actualMaximumPredecessor a' b'

def ActualDescentJointMonotone : Prop :=
  ∀ a a' : Ordinal.{0}, Ordinal.omega0 ≤ a → a ≤ a' → a' < epsilonZero →
    actualOrdinalNorm a ≤ actualOrdinalNorm a' →
      actualDescentStep a ≤ actualDescentStep a' ∧
      actualOrdinalNorm (actualDescentStep a) ≤ actualOrdinalNorm (actualDescentStep a')

def ActualReplacementCountJointMonotone : Prop :=
  ∀ a a' : Ordinal.{0}, a ≤ a' → a' < epsilonZero →
    actualOrdinalNorm a ≤ actualOrdinalNorm a' → actualReplacementCount a ≤ actualReplacementCount a'

def ControlIterateDoubleTowerGap : Prop :=
  ∀ L : Nat, 1 ≤ L → ∀ t : Nat, 2 ^ (2 ^ ((Phi^[L]) t)) ≤ (Phi^[L]) (t + 1)

def ActualTailSeparation : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → Order.IsSuccLimit a →
    (∀ n : Nat, 2 ^ (actualCollapse (a + (n : Ordinal))) <
      actualCollapse (a + ((n + 1 : Nat) : Ordinal))) ∧
    Function.Injective (fun n : Nat => actualCollapse (a + (n : Ordinal)))

end LogicLineages.OrdinalComparison.Targets
