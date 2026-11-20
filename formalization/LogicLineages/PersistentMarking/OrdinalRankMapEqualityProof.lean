module

public import LogicLineages.PersistentMarking.OrdinalRankMapEqualityTargets
public import LogicLineages.PersistentMarking.OrdinalRankSupportProof

public section

namespace LogicLineages.PersistentMarking.OrdinalRankMapEqualityProof
open OrdinalRankMapEqualityTargets OrdinalRankSupportProof

private theorem backwardsRank {α δ : Type} (r : α → α → Prop) (s : δ → δ → Prop)
    (f : α → δ) (lifts : ∀ q u, s u (f q) → ∃ t, r t q ∧ f t = u)
    {q : α} (source : Acc r q) :
    ∀ target : Acc s (f q), target.rank ≤ source.rank := by
  induction source with
  | intro q children ih =>
    intro target
    rw [target.rank_eq, Acc.rank_eq (Acc.intro q children)]
    apply Ordinal.iSup_le
    rintro ⟨u, edge⟩
    obtain ⟨t, original, literal⟩ := lifts q u edge
    subst u
    have bound := ih t original (target.inv edge)
    exact (Order.succ_le_succ bound).trans
      (Ordinal.le_iSup _ (⟨t, original⟩ : {v : α // r v q}))

theorem exact_RankEqualityFromSuccessorLifting : RankEqualityFromSuccessorLifting := by
  intro α δ r s f forwards lifts q source target
  exact le_antisymm (exact_RankOfRelationMap f forwards source target)
    (backwardsRank r s f lifts source target)

#print axioms exact_RankEqualityFromSuccessorLifting

end LogicLineages.PersistentMarking.OrdinalRankMapEqualityProof
