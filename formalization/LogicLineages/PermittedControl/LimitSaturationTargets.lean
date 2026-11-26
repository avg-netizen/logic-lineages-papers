module
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.LimitSaturationTargets
open OrdinalComparison

/-- Complete Paper17 limit saturation and both-argument monotonicity. -/
def LimitSaturation : Prop :=
  (∀ a : Ordinal.{0}, a < epsilonZero → Order.IsSuccLimit a → ∀ b : Nat,
    actualOrdinalNorm (actualMaximumPredecessor a b) = b) ∧
  (∀ a : Ordinal.{0}, a < epsilonZero → Order.IsSuccLimit a →
    StrictMono (actualMaximumPredecessor a)) ∧
  (∀ a a' : Ordinal.{0}, 0 < a → a ≤ a' → a' < epsilonZero →
    ∀ b b' : Nat, b ≤ b' →
      actualMaximumPredecessor a b ≤ actualMaximumPredecessor a' b')


end LogicLineages.PermittedControl.LimitSaturationTargets
