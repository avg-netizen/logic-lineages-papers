module
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.CollapseFoundationTargets
open OrdinalComparison

/-- Full current18 f:lem:collapse-estimates. Controlled strictness retains
its actual norm bound; there is no global ordinal monotonicity assertion. -/
def CollapseEstimates : Prop :=
  (∀ a : Ordinal.{0}, a < epsilonZero → ∀ b : Ordinal.{0}, b < a →
    actualOrdinalNorm b ≤ Phi (actualOrdinalNorm a) →
    actualCollapse b + 1 ≤ actualCollapse a) ∧
  (∀ n : Nat, actualCollapse (n : Ordinal.{0}) = n) ∧
  (∀ a : Ordinal.{0}, a < epsilonZero → actualOrdinalNorm a ≤ actualCollapse a) ∧
  (∀ a : Ordinal.{0}, a < epsilonZero → ∀ k : Nat,
    actualCollapse a + k ≤ actualCollapse (a + (k : Ordinal))) ∧
  (∀ a : Ordinal.{0}, a < epsilonZero → Ordinal.omega0 ≤ a →
    Phi (actualOrdinalNorm a) < actualCollapse a)

/-- Full current18 f:lem:limit-saturation, including monotonicity in BOTH
arguments on their actual positive predecessor domain. -/
def LimitSaturation : Prop :=
  (∀ a : Ordinal.{0}, a < epsilonZero → Order.IsSuccLimit a → ∀ b : Nat,
    actualOrdinalNorm (actualMaximumPredecessor a b) = b) ∧
  (∀ a : Ordinal.{0}, a < epsilonZero → Order.IsSuccLimit a →
    StrictMono (actualMaximumPredecessor a)) ∧
  (∀ a a' : Ordinal.{0}, 0 < a → a ≤ a' → a' < epsilonZero →
    ∀ b b' : Nat, b ≤ b' →
      actualMaximumPredecessor a b ≤ actualMaximumPredecessor a' b')

/-- Full current18 f:thm:single-predecessor. All finite tails include n=0
and use ordinary addition; the maximum is independently defined. -/
def SinglePredecessor : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → Order.IsSuccLimit a → ∀ n : Nat,
    actualCollapse (a + (n : Ordinal)) =
      actualCollapse (actualMaximumPredecessor a (Phi (actualOrdinalNorm a + n))) + 1

end LogicLineages.StandardControlCurrent.CollapseFoundationTargets
