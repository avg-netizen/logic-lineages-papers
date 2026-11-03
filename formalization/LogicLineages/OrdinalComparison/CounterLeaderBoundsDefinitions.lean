module
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderBounds

/-- Explicit sufficient tail, strengthened from the exact-identity component.
No claim that this is the minimal source threshold is made. -/
def threshold (n c : Nat) : Nat :=
  max (CounterLeaderExpansion.threshold n c) (2*c+10)

end LogicLineages.OrdinalComparison.CounterLeaderBounds
