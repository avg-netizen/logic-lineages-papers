module

public import LogicLineages.NativeModule.PersistentMarking.ConservativeBinderProof
public import LogicLineages.NativeModule.PersistentMarking.RefinementMarkProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ConservativeCases
open Spine NameBridge ConservativeResults ConservativeListSupport ConservativeOwnerSupport
open ExtendedMeasure

theorem case_coverageCons (S : Signature) (n : Nat) (small : Smaller S n)
    (ha : At owners i q)
    (hc : ExtendedTree S (.strict q x))
    (hs : ExtendedTree S (.coverage owners xs))
    (hn : 1 + treeSize hc + treeSize hs = n) : Result S (.coverage owners (.cons x xs)) := by
  intro qs hq ho
  obtain ⟨q,hat,href⟩ := baseAt hq ha
  obtain ⟨href⟩ := href
  exact .cons hat (small _ hc (by omega) q href ho.1) (small _ hs (by omega) qs hq ho.2)

theorem case_wholeNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.whole f base extras .nil) := by
  intro qb qe τ href ho
  exact .nil

theorem case_wholeCons (S : Signature) (n : Nat) (small : Smaller S n)
    (hw : ExtendedTree S (.weak (.marked f q.type base extras) q))
    (hs : ExtendedTree S (.whole f base extras qs))
    (hn : 1 + treeSize hw + treeSize hs = n) : Result S (.whole f base extras (.cons q qs)) := by
  intro qb qe τ href ho
  have hrt := RefinementTransitivitySupport.retype q.type href
  exact .cons (small _ hw (by omega) _ hrt ho.1) (small _ hs (by omega) qb qe τ href ho.2)

theorem case_orderedNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.ordered .nil .nil) := by
  trivial

theorem case_orderedCons (S : Signature) (n : Nat) (small : Smaller S n)
    (hw : ExtendedTree S (.weak q t))
    (hs : ExtendedTree S (.ordered qs ts))
    (hn : 1 + treeSize hw + treeSize hs = n) : Result S (.ordered (.cons q qs) (.cons t ts)) := by
  trivial
end LogicLineages.PersistentMarking.ConservativeCases
