import LogicLineages.PersistentMarking.Comparison
namespace LogicLineages.PersistentMarking.Spine

/-- Literal order-preserving prefix, not a submultiset. -/
inductive Prefix : Args → Args → Prop where
  | nil : Prefix .nil xs
  | cons : Prefix xs ys → Prefix (.cons x xs) (.cons x ys)

/-- Exact positional permutation; every occurrence is removed once. -/
inductive Permutation : Args → Args → Prop where
  | nil : Permutation .nil .nil
  | cons : Remove ys x rest → Permutation xs rest → Permutation (.cons x xs) ys

inductive PrefixCopy (f : Head) (base extras : Args) : Ty → Expr → Prop where
  | intro : Prefix pref extras → PrefixCopy f base extras τ (.marked f τ base pref)

inductive PrefixTuple (f : Head) (base extras : Args) : List Ty → Args → Prop where
  | nil : PrefixTuple f base extras [] .nil
  | cons : PrefixCopy f base extras σ q → PrefixTuple f base extras types qs →
      PrefixTuple f base extras (σ::types) (.cons q qs)

inductive PrefixCopies (f : Head) (base extras : Args) : Args → Prop where
  | nil : PrefixCopies f base extras .nil
  | cons : PrefixCopy f base extras q.type q → PrefixCopies f base extras qs →
      PrefixCopies f base extras (.cons q qs)

end LogicLineages.PersistentMarking.Spine
