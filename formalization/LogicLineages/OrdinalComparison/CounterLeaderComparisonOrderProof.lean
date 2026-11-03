module
public import LogicLineages.OrdinalComparison.CounterLeaderComparisonTargets
public import LogicLineages.OrdinalComparison.CounterLeaderCollisionProof
public import LogicLineages.OrdinalComparison.CounterUnequalLeaderOrderProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderComparison.Proof
open CounterLeaderExpansion

private theorem equal_rank_order (n m c e t u : Nat)
    (ht : CubicLeaderRecognition.leaderTail n c e ≤ t)
    (hu : CubicLeaderRecognition.leaderTail m e c ≤ u)
    (hh : leader n c t = leader m e u) (hnm : n < m) :
    count (n+3) c t < count (m+3) e u := by
  let k := m-n
  have hm : n+k = m := Nat.add_sub_of_le hnm.le
  have h := CounterLeaderCollision.Proof.actualCrossRankCollision k n e c u t
    (by simpa only [hm] using hu) ht (by simpa only [hm] using hh.symm)
  have hk : 0 < k := by dsimp [k]; omega
  simpa only [hm] using (h.2.2.2 hk).2

theorem actualCounterStrictOrder : Targets.ActualCounterStrictOrder := by
  intro n m c e t u ht hu
  have htb : CounterLeaderBounds.threshold n c ≤ t := (Nat.le_max_left _ _).trans ht
  have hub : CounterLeaderBounds.threshold m e ≤ u := (Nat.le_max_left _ _).trans hu
  have htl : CubicLeaderRecognition.leaderTail n c e ≤ t := (Nat.le_max_right _ _).trans ht
  have hul : CubicLeaderRecognition.leaderTail m e c ≤ u := (Nat.le_max_right _ _).trans hu
  by_cases hh : leader n c t = leader m e u
  · constructor
    · intro hc
      refine Or.inr ⟨hh,?_⟩
      rcases lt_trichotomy n m with hlt | heq | hgt
      · exact hlt
      · subst m
        have he := (SameRankLeaderRecognition.Proof.actualSameRankRecognition n c e t u htl hul).2 hh
        omega
      · have hg := equal_rank_order m n e c u t hul htl hh.symm hgt
        omega
    · intro h
      rcases h with hl | ⟨_,hn⟩
      · exact False.elim ((ne_of_lt hl) hh)
      · exact equal_rank_order n m c e t u htl hul hh hn
  · have h := (CounterUnequalLeaderOrder.Proof.actualUnequalLeaderOrder n m c e t u htb hub hh).1
    constructor
    · intro hc
      exact Or.inl (h.mp hc)
    · intro hh'
      rcases hh' with hl | ⟨he,_⟩
      · exact h.mpr hl
      · exact False.elim (hh he)

end LogicLineages.OrdinalComparison.CounterLeaderComparison.Proof
