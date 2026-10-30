module
public import LogicLineages.OrdinalComparison.OptimizedMaximumDefinitions
public import LogicLineages.OrdinalComparison.ActualOrdinalNormDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 limitmass proof 613–622: exact first suffix for a genuine nonzero
limit exponent. The budget-one edge remains present; exponent positivity is
concluded only for budget at least two. -/
def ActualLimitExponentMaximum : Prop :=
  ∀ beta : Ordinal.{0}, Order.IsSuccLimit beta → beta < epsilonZero →
    ∀ budget : Nat, 0 < budget →
      let delta := actualMaximumPredecessor beta (budget-1)
      Ordinal.omega0 ^ beta < epsilonZero ∧ delta < beta ∧
      actualOrdinalNorm delta = budget-1 ∧
      actualMaximumPredecessor (Ordinal.omega0 ^ beta) budget = Ordinal.omega0 ^ delta ∧
      actualOrdinalNorm (Ordinal.omega0 ^ delta) = budget ∧
      (2 ≤ budget → 0 < delta)

def ActualLimitExponentBudgetStrict : Prop :=
  ∀ beta : Ordinal.{0}, Order.IsSuccLimit beta → beta < epsilonZero →
    ∀ a b : Nat, 0 < a → a < b →
      actualMaximumPredecessor beta (a-1) < actualMaximumPredecessor beta (b-1)

end LogicLineages.OrdinalComparison.Targets
