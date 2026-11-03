module
public import LogicLineages.OrdinalComparison.SameRankLeaderRecognitionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.SameRankLeaderRecognition.Targets
open CounterLeaderExpansion

/-- Fixed-rank, fixed-mass input order for the literal original chain.
Only the original expansion tail is required, not a new eventual oracle. -/
def ActualFixedRankStrictInputs : Prop := ∀ n c t u : Nat,
  threshold n c ≤ t → threshold n c ≤ u → t < u →
  bottomInput n c t < bottomInput n c u ∧
  leaderPreimage n c t < leaderPreimage n c u ∧
  leader n c t < leader n c u

/-- At equal ranks, equal actual leaders recognize both original mass and
original input, hence the whole actual count. Cross-mass equality uses the
already explicit leaderTail on each side. No cross-rank collision is claimed. -/
def ActualSameRankRecognition : Prop := ∀ n c e t u : Nat,
  CubicLeaderRecognition.leaderTail n c e ≤ t →
  CubicLeaderRecognition.leaderTail n e c ≤ u →
  (leader n c t = leader n e u ↔ c = e ∧ t = u) ∧
  (leader n c t = leader n e u → count (n+3) c t = count (n+3) e u)

end LogicLineages.OrdinalComparison.SameRankLeaderRecognition.Targets
