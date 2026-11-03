module
public import LogicLineages.OrdinalComparison.CounterLeaderBoundsDefinitions
public import LogicLineages.OrdinalComparison.CubicLeaderRecognitionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderComparison
/-- Explicit pair-dependent sufficient tail; no minimality assertion. -/
def threshold (n c e : Nat) : Nat :=
  max (CounterLeaderBounds.threshold n c) (CubicLeaderRecognition.leaderTail n c e)
end LogicLineages.OrdinalComparison.CounterLeaderComparison
