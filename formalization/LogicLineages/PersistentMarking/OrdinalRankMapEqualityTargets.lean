module

public import LogicLineages.PersistentMarking.OrdinalRankSupportTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.OrdinalRankMapEqualityTargets

def RankEqualityFromSuccessorLifting : Prop :=
  ∀ {α δ : Type} (r : α → α → Prop) (s : δ → δ → Prop) (f : α → δ),
    (∀ {q t}, r t q → s (f t) (f q)) →
    (∀ q u, s u (f q) → ∃ t, r t q ∧ f t = u) →
    ∀ q (source : Acc r q) (target : Acc s (f q)), source.rank = target.rank

end LogicLineages.PersistentMarking.OrdinalRankMapEqualityTargets
