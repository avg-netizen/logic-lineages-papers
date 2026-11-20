module

public import LogicLineages.PersistentMarking.OrdinalPredecessorClosedRankTargets
public import LogicLineages.PersistentMarking.OrdinalRankSupportProof

public section

namespace LogicLineages.PersistentMarking.OrdinalPredecessorClosedRankProof
open OrdinalPredecessorClosedRankTargets OrdinalRankSupportProof

private theorem fullRankLE {α : Type} (r : α → α → Prop) (guard : α → Prop)
    (closed : ∀ {source target}, guard source → r target source → guard target)
    {q : α} (full : Acc r q) :
    ∀ (inGuard : guard q) (restricted : Acc (Restrict r guard) ⟨q, inGuard⟩),
      full.rank ≤ restricted.rank := by
  induction full with
  | intro q predecessors ih =>
    intro inGuard restricted
    rw [Acc.rank_eq (Acc.intro q predecessors), restricted.rank_eq]
    apply Ordinal.iSup_le
    intro target
    let guardedTarget : {t : Subtype guard // Restrict r guard t ⟨q, inGuard⟩} :=
      ⟨⟨target.val, closed inGuard target.property⟩, target.property⟩
    have child := ih target.val target.property guardedTarget.val.property
      (restricted.inv guardedTarget.property)
    exact (Order.succ_le_succ child).trans (Ordinal.le_iSup _ guardedTarget)

theorem exact_PredecessorClosedRankEquality : PredecessorClosedRankEquality := by
  intro α r guard closed q full restricted
  apply le_antisymm
  · exact fullRankLE r guard closed full q.property restricted
  · exact exact_RankOfRelationMap Subtype.val (fun h => h) restricted full

#print axioms exact_PredecessorClosedRankEquality

end LogicLineages.PersistentMarking.OrdinalPredecessorClosedRankProof
