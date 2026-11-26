import LogicLineages.PersistentMarking.TargetExtrasResults
namespace LogicLineages.PersistentMarking.TargetExtrasCases
open Spine NameBridge TargetExtrasRootSupport TargetExtrasResults ExtendedMeasure

theorem case_strictIntro (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S q σ)
    (ht : PaperTerm S t σ)
    (hm : mark q = some r)
    (hc : ExtendedTree S (.weak r t))
    (hn : 1 + treeSize hc = n) : Result S (.strict q t) := by
  trivial

theorem case_matchingNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.matching .nil .nil) := by
  trivial

theorem case_matchingCons (S : Signature) (n : Nat) (small : Smaller S n)
    (hr : Remove targets y rest)
    (hw : ExtendedTree S (.weak x y))
    (hm : ExtendedTree S (.matching xs rest))
    (hn : 1 + treeSize hw + treeSize hm = n) : Result S (.matching (.cons x xs) targets) := by
  trivial

theorem case_multisetReplace (S : Signature) (n : Nat) (small : Smaller S n)
    (hs : Split source kept removed)
    (ht : Split target matched added)
    (hnon : Nonempty removed)
    (hm : ExtendedTree S (.matching kept matched))
    (hc : ExtendedTree S (.coverage removed added))
    (hn : 1 + treeSize hm + treeSize hc = n) : Result S (.multiset source target) := by
  trivial

theorem case_coverageNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.coverage owners .nil) := by
  trivial

end LogicLineages.PersistentMarking.TargetExtrasCases
