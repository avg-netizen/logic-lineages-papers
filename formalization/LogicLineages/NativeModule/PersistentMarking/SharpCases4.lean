module

public import LogicLineages.NativeModule.PersistentMarking.SharpBinderProof
public import LogicLineages.NativeModule.PersistentMarking.RefinementMarkProof
public import LogicLineages.NativeModule.PersistentMarking.ExtraCompressionProof
public import LogicLineages.NativeModule.PersistentMarking.ExtendedEndpointProof

@[expose] public section

namespace LogicLineages.PersistentMarking.SharpCases
open Spine NameBridge SharpResults ConservativeListSupport ConservativeOwnerSupport
open ExtendedMeasure

theorem case_strictIntro (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S q σ)
    (ht : PaperTerm S t σ)
    (hm : mark q = some r)
    (hc : ExtendedTree S (.weak r t))
    (hn : 1 + treeSize hc = n) : Result S (.strict q t) := by
  intro q hq
  obtain ⟨r,hmq,href⟩ := RefinementMarkProof.refinementMarkReflection S _ _ _ ⟨hq⟩ hm
  obtain ⟨href⟩ := href
  obtain ⟨hc'⟩ := small _ hc (by omega) r href
  exact ⟨.strictIntro (refiningPaper hq hp) ht hmq hc'⟩

theorem case_matchingNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.matching .nil .nil) := by
  intro qs hq
  cases hq
  exact ⟨.matchingNil⟩

theorem case_matchingCons (S : Signature) (n : Nat) (small : Smaller S n)
    (hr : Remove targets y rest)
    (hw : ExtendedTree S (.weak x y))
    (hm : ExtendedTree S (.matching xs rest))
    (hn : 1 + treeSize hw + treeSize hm = n) : Result S (.matching (.cons x xs) targets) := by
  intro qs hq
  cases hq with
  | cons h hs =>
    obtain ⟨hw'⟩ := small _ hw (by omega) _ h
    obtain ⟨hm'⟩ := small _ hm (by omega) _ hs
    exact ⟨.matchingCons hr hw' hm'⟩

theorem case_multisetReplace (S : Signature) (n : Nat) (small : Smaller S n)
    (hs : Split source kept removed)
    (ht : Split target matched added)
    (hnon : Nonempty removed)
    (hm : ExtendedTree S (.matching kept matched))
    (hc : ExtendedTree S (.coverage removed added))
    (hn : 1 + treeSize hm + treeSize hc = n) : Result S (.multiset source target) := by
  intro qs hq
  obtain ⟨qk,qr,hsp,hk,hr⟩ := transportSplit hq hs
  obtain ⟨hk⟩ := hk
  obtain ⟨hr⟩ := hr
  obtain ⟨hm'⟩ := small _ hm (by omega) qk hk
  obtain ⟨hc'⟩ := small _ hc (by omega) qr hr
  exact ⟨.multisetReplace hsp ht (baseNonempty hr hnon) hm' hc'⟩

theorem case_coverageNil (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : Result S (.coverage owners .nil) := by
  intro qs hq
  exact ⟨.coverageNil⟩

end LogicLineages.PersistentMarking.SharpCases
