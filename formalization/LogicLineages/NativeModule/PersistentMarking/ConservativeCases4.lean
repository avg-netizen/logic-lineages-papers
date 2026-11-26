module

public import LogicLineages.NativeModule.PersistentMarking.ConservativeBinderProof
public import LogicLineages.NativeModule.PersistentMarking.RefinementMarkProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ConservativeCases
open Spine NameBridge ConservativeResults ConservativeListSupport ConservativeOwnerSupport
open ExtendedMeasure

theorem case_strictIntro (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S q σ)
    (ht : PaperTerm S t σ)
    (hm : mark q = some r)
    (hc : ExtendedTree S (.weak r t))
    (hn : 1 + treeSize hc = n) : Result S (.strict q t) := by
  intro q hq ho
  obtain ⟨r,hmq,href⟩ := RefinementMarkProof.refinementMarkReflection S _ _ _ ⟨hq⟩ hm
  obtain ⟨href⟩ := href
  exact .intro (refiningPaper hq hp) ht hmq (small _ hc (by omega) r href ho)

theorem case_matchingNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.matching .nil .nil) := by
  intro qs hq ho
  cases hq
  exact .nil

theorem case_matchingCons (S : Signature) (n : Nat) (small : Smaller S n)
    (hr : Remove targets y rest)
    (hw : ExtendedTree S (.weak x y))
    (hm : ExtendedTree S (.matching xs rest))
    (hn : 1 + treeSize hw + treeSize hm = n) : Result S (.matching (.cons x xs) targets) := by
  intro qs hq ho
  have hot := removeOrdinaryParts hr ho
  cases hq with
  | cons h hs => exact .cons hr (small _ hw (by omega) _ h hot.1) (small _ hm (by omega) _ hs hot.2)

theorem case_multisetReplace (S : Signature) (n : Nat) (small : Smaller S n)
    (hs : Split source kept removed)
    (ht : Split target matched added)
    (hnon : Nonempty removed)
    (hm : ExtendedTree S (.matching kept matched))
    (hc : ExtendedTree S (.coverage removed added))
    (hn : 1 + treeSize hm + treeSize hc = n) : Result S (.multiset source target) := by
  intro qs hq ho
  obtain ⟨qk,qr,hsp,hk,hr⟩ := transportSplit hq hs
  obtain ⟨hk⟩ := hk
  obtain ⟨hr⟩ := hr
  have hot := splitOrdinary ht ho
  exact .replace hsp ht (baseNonempty hr hnon) (small _ hm (by omega) qk hk hot.1) (small _ hc (by omega) qr hr hot.2)

theorem case_coverageNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.coverage owners .nil) := by
  intro qs hq ho
  exact .nil
end LogicLineages.PersistentMarking.ConservativeCases
