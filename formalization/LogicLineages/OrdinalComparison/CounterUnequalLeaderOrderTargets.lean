module
public import LogicLineages.OrdinalComparison.CounterUnequalLeaderOrderDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterUnequalLeaderOrder.Targets
open CounterLeaderExpansion

/-- Distinct actual leaders have the literal source exponential gap, without
any input-domain or equality-recognition assumption. -/
def ActualLeaderGap : Prop := ∀ n m c e t u : Nat,
  leader n c t < leader m e u →
  2 ^ (leader n c t + 1) ≤ leader m e u

/-- Actual counter order agrees with distinct leader order on exactly the
previously saved sufficient bounds tails. Ranks and masses are arbitrary. -/
def ActualUnequalLeaderOrder : Prop := ∀ n m c e t u : Nat,
  CounterLeaderBounds.threshold n c ≤ t →
  CounterLeaderBounds.threshold m e ≤ u →
  leader n c t ≠ leader m e u →
  (count (n+3) c t < count (m+3) e u ↔ leader n c t < leader m e u) ∧
  count (n+3) c t ≠ count (m+3) e u

end LogicLineages.OrdinalComparison.CounterUnequalLeaderOrder.Targets
