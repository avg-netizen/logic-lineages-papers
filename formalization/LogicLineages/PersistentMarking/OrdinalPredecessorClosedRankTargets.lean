module

public import LogicLineages.PersistentMarking.OrdinalRankSupportTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.OrdinalPredecessorClosedRankTargets

def Restrict {α : Type} (r : α → α → Prop) (guard : α → Prop)
    (target source : Subtype guard) : Prop :=
  r target.val source.val

def PredecessorClosedRankEquality : Prop :=
  ∀ {α : Type} (r : α → α → Prop) (guard : α → Prop),
    (∀ {source target}, guard source → r target source → guard target) →
    ∀ q : Subtype guard, ∀ (full : Acc r q.val) (restricted : Acc (Restrict r guard) q),
      full.rank = restricted.rank

end LogicLineages.PersistentMarking.OrdinalPredecessorClosedRankTargets
