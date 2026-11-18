import LogicLineages.PersistentMarking.TargetExtrasResults
namespace LogicLineages.PersistentMarking.TargetExtrasCases
open Spine NameBridge TargetExtrasRootSupport TargetExtrasResults ExtendedMeasure

theorem case_coverageCons (S : Signature) (n : Nat) (small : Smaller S n)
    (ha : At owners i q)
    (hc : ExtendedTree S (.strict q x))
    (hs : ExtendedTree S (.coverage owners xs))
    (hn : 1 + treeSize hc + treeSize hs = n) : Result S (.coverage owners (.cons x xs)) := by
  trivial

theorem case_wholeNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.whole f base extras .nil) := by
  trivial

theorem case_wholeCons (S : Signature) (n : Nat) (small : Smaller S n)
    (hw : ExtendedTree S (.weak (.marked f q.type base extras) q))
    (hs : ExtendedTree S (.whole f base extras qs))
    (hn : 1 + treeSize hw + treeSize hs = n) : Result S (.whole f base extras (.cons q qs)) := by
  trivial

theorem case_orderedNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.ordered .nil .nil) := by
  trivial

theorem case_orderedCons (S : Signature) (n : Nat) (small : Smaller S n)
    (hw : ExtendedTree S (.weak q t))
    (hs : ExtendedTree S (.ordered qs ts))
    (hn : 1 + treeSize hw + treeSize hs = n) : Result S (.ordered (.cons q qs) (.cons t ts)) := by
  trivial

end LogicLineages.PersistentMarking.TargetExtrasCases
