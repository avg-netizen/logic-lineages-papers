module
public import LogicLineages.OrdinalComparison.ActualLimitPredecessorTargets
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullSaturationTargets
open OrdinalComparison
/-- Complete current20 lem:saturation, with no additional monotonicity claim. -/
def FullSaturation : Prop :=
  (∀ a : Ordinal.{0}, a < epsilonZero → Order.IsSuccLimit a → ∀ b : Nat,
    actualOrdinalNorm (actualMaximumPredecessor a b) = b) ∧
  (∀ a : Ordinal.{0}, a < epsilonZero → Order.IsSuccLimit a →
    StrictMono (actualMaximumPredecessor a))
end LogicLineages.CartierObserverCurrent.FullSaturationTargets
