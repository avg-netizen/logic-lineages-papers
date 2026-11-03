module
public import LogicLineages.OrdinalComparison.CounterLeaderComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterFixedShiftComparison
/-- Explicit sufficient tail paying actual comparison, the smaller leader gap,
and every possible first upper residual at this original rank. -/
def threshold (n c e K : Nat) : Nat :=
  max (CounterLeaderComparison.threshold n c e) (max (4*K) (c+(n+3)+2*K+3))
end LogicLineages.OrdinalComparison.CounterFixedShiftComparison
