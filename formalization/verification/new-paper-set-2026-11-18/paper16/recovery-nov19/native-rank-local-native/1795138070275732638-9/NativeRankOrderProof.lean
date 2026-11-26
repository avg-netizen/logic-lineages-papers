import LogicLineages.PersistentMarking.NativeRankTargets

namespace LogicLineages.PersistentMarking.NativeRankOrderProof
open NativeIteratorStrictTargets NativeRankTargets

theorem recurrence : NativeRankRecurrence := by
  intro S τ s h
  exact h.rank_eq

theorem edgeDrop : NativeRankStrictEdge := by
  intro S τ s t h edge
  exact h.rank_lt_of_rel edge

theorem restriction : NativeRankRestriction := by
  intro S τ s h
  induction h with
  | intro s pred ih =>
    intro full
    change (Acc.intro s pred).rank ≤ full.rank
    rw [Acc.rank_eq (Acc.intro s pred), full.rank_eq]
    apply Ordinal.iSup_le
    intro t
    let v : {v : Spine.Expr // ConfinedPair.Strict S s.val v} := ⟨t.val.val, t.property⟩
    have hle := ih t.val t.property (full.inv v.property)
    exact (Order.succ_le_succ hle).trans (Ordinal.le_iSup _ v)

theorem successorWitness : NativeRankSuccessorWitness := by
  intro S τ s h β bound
  have hlt := (Order.lt_succ β).trans_le bound
  rw [recurrence S τ s h, Ordinal.lt_iSup_iff] at hlt
  obtain ⟨t, ht⟩ := hlt
  exact ⟨t.val, t.property, Order.lt_succ_iff.mp ht⟩

end LogicLineages.PersistentMarking.NativeRankOrderProof
