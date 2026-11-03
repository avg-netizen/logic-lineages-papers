module
public import LogicLineages.OrdinalComparison.CounterLeaderCollisionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterResidualDivergence
/-- Original expansion domain plus a quantitative bound for the actual first
upper residual. The lower input is constructed by the existing alignment. -/
def threshold (k m c K : Nat) : Nat :=
  max (CounterLeaderExpansion.threshold (m+k) c) (c+(m+k+3)+2*K+3)
end LogicLineages.OrdinalComparison.CounterResidualDivergence
