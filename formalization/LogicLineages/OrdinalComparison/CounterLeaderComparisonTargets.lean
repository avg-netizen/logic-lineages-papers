module
public import LogicLineages.OrdinalComparison.CounterLeaderComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderComparison.Targets
open CounterLeaderExpansion

/-- Exact source ordering: leader first, rank for an actual leader tie. -/
def ActualCounterStrictOrder : Prop := ∀ n m c e t u : Nat,
  CounterLeaderComparison.threshold n c e ≤ t →
  CounterLeaderComparison.threshold m e c ≤ u →
  (count (n+3) c t < count (m+3) e u ↔
    leader n c t < leader m e u ∨ (leader n c t = leader m e u ∧ n < m))

/-- Exact equality on the explicit pair-dependent tails, with actual original
rank, mass and input recognized. Not a whole-domain uniqueness assertion. -/
def ActualCounterEquality : Prop := ∀ n m c e t u : Nat,
  CounterLeaderComparison.threshold n c e ≤ t →
  CounterLeaderComparison.threshold m e c ≤ u →
  (count (n+3) c t = count (m+3) e u ↔ leader n c t = leader m e u ∧ n = m) ∧
  (count (n+3) c t = count (m+3) e u ↔ n = m ∧ c = e ∧ t = u)

end LogicLineages.OrdinalComparison.CounterLeaderComparison.Targets
