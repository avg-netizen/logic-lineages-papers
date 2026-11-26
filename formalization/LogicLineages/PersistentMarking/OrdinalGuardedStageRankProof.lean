module

public import LogicLineages.PersistentMarking.OrdinalGuardedStageRankTargets

public section

namespace LogicLineages.PersistentMarking.OrdinalGuardedStageRankProof
open OrdinalGuardedStageRankTargets

theorem exact_GuardedStageRank : GuardedStageRankExact := by
  intro α r domain stage law closed
  have equivalent : ∀ a q, stage a q ↔ domain q ∧ ∃ h : Acc r q, h.rank ≤ a := by
    intro a
    refine Ordinal.lt_wf.induction
      (C := fun a => ∀ q, stage a q ↔ domain q ∧ ∃ h : Acc r q, h.rank ≤ a) a ?_
    intro a ih q
    constructor
    · intro member
      obtain ⟨guard, prior⟩ := (law a q).mp member
      have access : Acc r q := Acc.intro q fun t edge => by
        obtain ⟨b, earlier, stageT⟩ := prior t edge
        obtain ⟨_, child, _⟩ := (ih b earlier t).mp stageT
        exact child
      refine ⟨guard, access, ?_⟩
      rw [access.rank_eq]
      apply Ordinal.iSup_le
      intro t
      obtain ⟨b, earlier, stageT⟩ := prior t.val t.property
      obtain ⟨_, child, rankChild⟩ := (ih b earlier t.val).mp stageT
      have childEarlier : (access.inv t.property).rank < a := rankChild.trans_lt earlier
      exact Order.succ_le_of_lt childEarlier
    · rintro ⟨guard, access, bound⟩
      refine (law a q).mpr ⟨guard, ?_⟩
      intro t edge
      let child := access.inv edge
      have earlier : child.rank < a := (access.rank_lt_of_rel edge).trans_le bound
      exact ⟨child.rank, earlier, (ih child.rank earlier t).mpr ⟨closed guard edge, child, le_rfl⟩⟩
  refine ⟨equivalent, ?_, ?_⟩
  · intro q h guard
    refine ⟨(equivalent h.rank q).mpr ⟨guard, h, le_rfl⟩, ?_⟩
    intro a membership
    obtain ⟨_, _, bound⟩ := (equivalent a q).mp membership
    exact bound
  · intro q guard isolated
    exact (law 0 q).mpr ⟨guard, fun t edge => (isolated t edge).elim⟩

#print axioms exact_GuardedStageRank

end LogicLineages.PersistentMarking.OrdinalGuardedStageRankProof
