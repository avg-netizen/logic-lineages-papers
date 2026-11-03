module
public import LogicLineages.OrdinalComparison.CounterLeaderCollisionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderCollision.Targets
open CounterLeaderExpansion

/-- Literal list splitting at the smaller rank, with every original value and
rank retained and every actual intermediate domain derived. -/
def ExactChainSplitting : Prop := ∀ k m c t : Nat, threshold (m+k) c ≤ t →
  entries (m+k) c t = upperEntries k m c t ++ entries m c (alignedInput k m c t) ∧
  bottomInput (m+k) c t = bottomInput m c (alignedInput k m c t) ∧
  leader (m+k) c t = leader m c (alignedInput k m c t) ∧
  t ≤ alignedInput k m c t ∧ threshold m c ≤ alignedInput k m c t ∧
  (upperEntries k m c t).length = k ∧
  (∀ p ∈ upperEntries k m c t, m+3 < p.1 ∧ p.1 ≤ m+k+3 ∧
    t ≤ p.2 ∧ c+2*p.1+1 ≤ p.2) ∧
  residuals (m+k) c t = upperResiduals k m c t ++ residuals m c (alignedInput k m c t)

/-- Equal actual leaders force the original mass and aligned input, then give
the exact signed count difference. A nonempty upper chain has actual positive
counts, so the higher rank is strictly larger. No unequal-leader claim. -/
def ActualCrossRankCollision : Prop := ∀ k m c e t u : Nat,
  CubicLeaderRecognition.leaderTail (m+k) c e ≤ t →
  CubicLeaderRecognition.leaderTail m e c ≤ u →
  leader (m+k) c t = leader m e u →
  c = e ∧ u = alignedInput k m c t ∧
  (count (m+k+3) c t : Int) - (count (m+3) e u : Int) =
    ((upperResiduals k m c t).sum : Int) ∧
  (0 < k → 0 < (upperResiduals k m c t).sum ∧
    count (m+3) e u < count (m+k+3) c t)

end LogicLineages.OrdinalComparison.CounterLeaderCollision.Targets
