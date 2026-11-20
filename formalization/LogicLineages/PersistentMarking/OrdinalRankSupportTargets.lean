module

public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

namespace LogicLineages.PersistentMarking.OrdinalRankSupportTargets

def RankOfRelationMap : Prop :=
  ∀ {α δ : Type} {r : α → α → Prop} {s : δ → δ → Prop} (f : α → δ),
    (∀ {q t}, r t q → s (f t) (f q)) →
    ∀ {q : α} (h : Acc r q) (hf : Acc s (f q)), h.rank ≤ hf.rank

def RankImmediateSuccessor : Prop :=
  ∀ {α : Type} {r : α → α → Prop} {q : α} (h : Acc r q) (β : Ordinal.{0}),
    Order.succ β ≤ h.rank →
      ∃ (t : α) (edge : r t q), β ≤ (h.inv edge).rank

def CountableRankPrefix : Prop :=
  ∀ {α : Type} [Countable α] {r : α → α → Prop} {q : α} (h : Acc r q),
    Countable {β : Ordinal.{0} // β < h.rank}

end LogicLineages.PersistentMarking.OrdinalRankSupportTargets
