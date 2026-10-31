module
public import LogicLineages.OrdinalComparison.WWFiniteTailMonotonicityTargets
public import LogicLineages.OrdinalComparison.ActualCollapseBounds

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem finite_tail_step (a : Ordinal) (ha : a < epsilonZero) (k : Nat) :
    actualCollapse (a + (k : Ordinal)) + 1 ≤
      actualCollapse (a + ((k + 1 : Nat) : Ordinal)) := by
  have hk := actualFiniteTailClosureNorm a ha k
  have hs := actualFiniteTailClosureNorm a ha (k + 1)
  apply actualCollapse_controlledStrictness _ hs.1 _
  · exact add_lt_add_right (by exact_mod_cast Nat.lt_succ_self k) a
  · rw [hk.2, hs.2]
    have hp := self_lt_Phi (actualOrdinalNorm a + (k + 1))
    omega

theorem actualCollapseFiniteTailIncrement : Targets.ActualCollapseFiniteTailIncrement := by
  intro a ha k
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := finite_tail_step a ha k
    omega

theorem actualCollapseFiniteTailMonotone : Targets.ActualCollapseFiniteTailMonotone := by
  intro a ha r s hrs
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hrs ih =>
    have hs := finite_tail_step a ha s
    exact ih.trans (Nat.le_trans (Nat.le_add_right _ 1) hs)

end LogicLineages.OrdinalComparison
