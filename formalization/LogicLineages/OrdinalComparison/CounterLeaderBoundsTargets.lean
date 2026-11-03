module
public import LogicLineages.OrdinalComparison.CounterLeaderBoundsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderBounds.Targets
open CounterLeaderExpansion

/-- The full actual residual list telescopes along actual entry norms; the
positive cubic correction is proved on the explicit strengthened tail. -/
def ActualResidualBounds : Prop :=
  (∀ n c t : Nat, t + (residuals n c t).sum ≤ leaderPreimage n c t) ∧
  (∀ n c t : Nat, CounterLeaderBounds.threshold n c ≤ t →
    (c+1)/2 < (residuals n c t).sum)

/-- Exactly the source's strict rational half/three-quarter inequalities,
written without division rounding: H < 2E and 4E < 3H. The explicit tail is
sufficient, not claimed minimal. No equal-leader recognition premise/claim. -/
def StrictActualLeaderBounds : Prop := ∀ n c t : Nat,
  CounterLeaderBounds.threshold n c ≤ t →
  leader n c t < 2 * count (n+3) c t ∧
  4 * count (n+3) c t < 3 * leader n c t

end LogicLineages.OrdinalComparison.CounterLeaderBounds.Targets
