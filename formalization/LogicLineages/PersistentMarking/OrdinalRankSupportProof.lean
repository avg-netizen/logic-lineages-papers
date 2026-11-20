module

public import LogicLineages.PersistentMarking.OrdinalRankSupportTargets

public section

namespace LogicLineages.PersistentMarking.OrdinalRankSupportProof
open OrdinalRankSupportTargets

theorem exact_RankOfRelationMap : RankOfRelationMap := by
  intro α δ r s f mapEdge q h
  induction h with
  | intro q pred ih =>
    intro hf
    rw [Acc.rank_eq (Acc.intro q pred), hf.rank_eq]
    apply Ordinal.iSup_le
    intro t
    let ft : {b : δ // s b (f q)} := ⟨f t.val, mapEdge t.property⟩
    have rankLE := ih t.val t.property (hf.inv ft.property)
    exact (Order.succ_le_succ rankLE).trans (Ordinal.le_iSup _ ft)

theorem exact_RankImmediateSuccessor : RankImmediateSuccessor := by
  intro α r q h β bound
  have ht := (Order.lt_succ β).trans_le bound
  rw [h.rank_eq, Ordinal.lt_iSup_iff] at ht
  obtain ⟨t, ht⟩ := ht
  exact ⟨t.val, t.property, Order.lt_succ_iff.mp ht⟩

private theorem countableSuccessor (o : Ordinal.{0})
    (countablePrefix : Countable {β : Ordinal.{0} // β < o}) :
    Countable {β : Ordinal.{0} // β < Order.succ o} := by
  letI := countablePrefix
  let send : Option {β : Ordinal.{0} // β < o} → {β : Ordinal.{0} // β < Order.succ o}
    | none => ⟨o, Order.lt_succ o⟩
    | some β => ⟨β.val, β.property.trans (Order.lt_succ o)⟩
  refine Function.Surjective.countable (f := send) ?_
  intro β
  rcases (Order.lt_succ_iff.mp β.property).eq_or_lt with he | hl
  · exact ⟨none, Subtype.ext he.symm⟩
  · exact ⟨some ⟨β.val, hl⟩, rfl⟩

theorem exact_CountableRankPrefix : CountableRankPrefix := by
  intro α countableCarrier r q h
  letI : Countable α := countableCarrier
  induction h with
  | intro q pred ih =>
    let Children := {t : α // r t q}
    let level (t : Children) := Order.succ (pred t.val t.property).rank
    let Segment (t : Children) := {β : Ordinal.{0} // β < level t}
    letI segmentCountable (t : Children) : Countable (Segment t) :=
      countableSuccessor _ (ih t.val t.property)
    rw [Acc.rank_eq (Acc.intro q pred)]
    change Countable {β : Ordinal.{0} // β < ⨆ t : Children, level t}
    let send : (Σ t : Children, Segment t) → {β : Ordinal.{0} // β < ⨆ t : Children, level t} :=
      fun ⟨t, β⟩ => ⟨β.val, β.property.trans_le (Ordinal.le_iSup level t)⟩
    refine Function.Surjective.countable (f := send) ?_
    intro β
    obtain ⟨t, ht⟩ := Ordinal.lt_iSup_iff.mp β.property
    exact ⟨⟨t, ⟨β.val, ht⟩⟩, rfl⟩

#print axioms exact_RankOfRelationMap
#print axioms exact_RankImmediateSuccessor
#print axioms exact_CountableRankPrefix

end LogicLineages.PersistentMarking.OrdinalRankSupportProof
