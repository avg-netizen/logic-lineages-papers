module
public import LogicLineages.OrdinalComparison.CounterLeaderComparisonDefinitions
public import LogicLineages.OrdinalComparison.CounterLeaderCollisionDefinitions
public import LogicLineages.OrdinalComparison.CounterFixedShiftComparisonDefinitions
public import LogicLineages.OrdinalComparison.CounterResidualDivergenceDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterSourceTheorem
/-- Uniform common sufficient tail for the two original ranks and masses. -/
def commonTail (n m c e : Nat) : Nat :=
  max (CounterLeaderComparison.threshold n c e) (CounterLeaderComparison.threshold m e c)
end LogicLineages.OrdinalComparison.CounterSourceTheorem
