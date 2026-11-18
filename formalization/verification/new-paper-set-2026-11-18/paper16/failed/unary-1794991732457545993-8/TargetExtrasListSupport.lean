import LogicLineages.PersistentMarking.TargetExtrasTargets
import LogicLineages.PersistentMarking.UnaryTransportSupport
namespace LogicLineages.PersistentMarking.TargetExtrasListSupport
open Spine

theorem prefixSuffix {xs ys : Args} (h : Prefix xs ys) : ∃ tail, ys = xs.append tail := by
  induction h with
  | nil => exact ⟨_,rfl⟩
  | cons hp ih => obtain ⟨tail,rfl⟩ := ih; exact ⟨tail,rfl⟩

theorem orderedPrefix {S : Signature} {xs ys pref : Args}
    (h : ExtendedOrderedTree S xs ys) (hp : Prefix pref ys) :
    ∃ source, Prefix source xs ∧ _root_.Nonempty (ExtendedOrderedTree S source pref) := by
  induction hp generalizing xs with
  | nil => exact ⟨.nil,.nil,⟨.orderedNil⟩⟩
  | cons hp ih =>
    cases h with
    | orderedCons he hs =>
      obtain ⟨source,hpre,⟨ht⟩⟩ := ih hs
      exact ⟨.cons _ source,.cons hpre,⟨.orderedCons he ht⟩⟩

theorem wholePrefix {S : Signature} {f : Head} {base extras ys pref : Args}
    (h : ExtendedWholeTree S f base extras ys) (hp : Prefix pref ys) :
    _root_.Nonempty (ExtendedWholeTree S f base extras pref) := by
  induction hp with
  | nil => exact ⟨.wholeNil⟩
  | cons hp ih =>
    cases h with
    | wholeCons he hs => obtain ⟨ht⟩ := ih hs; exact ⟨.wholeCons he ht⟩

theorem orderedInsert {S : Signature} {ys rest xs : Args} {a b : Expr}
    (hr : Remove ys b rest) (he : ExtendedWeakTree S a b) (h : ExtendedOrderedTree S xs rest) :
    ∃ source, Remove source a xs ∧ _root_.Nonempty (ExtendedOrderedTree S source ys) := by
  induction hr generalizing xs with
  | here => exact ⟨.cons a xs,.here,⟨.orderedCons he h⟩⟩
  | there hr ih =>
    cases h with
    | orderedCons hh ht =>
      obtain ⟨source,hs,⟨ht'⟩⟩ := ih he ht
      exact ⟨.cons _ source,.there hs,⟨.orderedCons hh ht'⟩⟩

theorem orderedPermutation {S : Signature} {xs ys zs : Args}
    (h : ExtendedOrderedTree S xs ys) (hp : Permutation ys zs) :
    ∃ source, Permutation xs source ∧ _root_.Nonempty (ExtendedOrderedTree S source zs) := by
  induction hp generalizing xs with
  | nil => cases h; exact ⟨.nil,.nil,⟨.orderedNil⟩⟩
  | cons hr hp ih =>
    cases h with
    | orderedCons he hs =>
      obtain ⟨source,hperm,⟨ht⟩⟩ := ih hs
      obtain ⟨source',hremove,⟨hout⟩⟩ := orderedInsert hr he ht
      exact ⟨source',.cons hremove hperm,⟨hout⟩⟩

theorem wholeInsert {S : Signature} {f : Head} {base extras ys rest : Args} {q : Expr}
    (hr : Remove ys q rest) (he : ExtendedWeakTree S (.marked f q.type base extras) q)
    (h : ExtendedWholeTree S f base extras rest) :
    _root_.Nonempty (ExtendedWholeTree S f base extras ys) := by
  induction hr with
  | here => exact ⟨.wholeCons he h⟩
  | there hr ih =>
    cases h with
    | wholeCons hh ht => obtain ⟨ht'⟩ := ih he ht; exact ⟨.wholeCons hh ht'⟩

theorem wholePermutation {S : Signature} {f : Head} {base extras ys zs : Args}
    (h : ExtendedWholeTree S f base extras ys) (hp : Permutation ys zs) :
    _root_.Nonempty (ExtendedWholeTree S f base extras zs) := by
  induction hp with
  | nil => exact ⟨.wholeNil⟩
  | cons hr hp ih =>
    cases h with
    | wholeCons he hs => obtain ⟨ht⟩ := ih hs; exact wholeInsert hr he ht

theorem prefixPaper {S : Signature} {f : Head} {τ ρ : Ty} {base extras pref : Args}
    (hp : PaperTerm S (.marked f τ base extras) τ) (hpre : Prefix pref extras) :
    PaperTerm S (.marked f ρ base pref) ρ := by
  obtain ⟨hr⟩ := OwnerRefinementProof.prefixOmission S f ρ base extras pref
    (AuxiliaryReflexivityProof.retypePaper S f τ ρ base extras hp) hpre
  exact (RefinementSubstitutionSupport.endpoints hr).2

theorem permutationPaper {S : Signature} {f : Head} {τ : Ty} {base extras reordered : Args}
    (hp : PaperTerm S (.marked f τ base extras) τ) (hperm : Permutation extras reordered) :
    PaperTerm S (.marked f τ base reordered) τ := by
  obtain ⟨hr⟩ := OwnerRefinementProof.permutation S f τ base extras reordered hp hperm
  exact (RefinementSubstitutionSupport.endpoints hr).2

theorem copiesPaper {S : Signature} {f : Head} {τ : Ty} {base extras copies : Args}
    (hp : PaperTerm S (.marked f τ base extras) τ) (hc : PrefixCopies f base extras copies) :
    PaperTerm S (.marked f τ base (extras.append copies)) τ := by
  obtain ⟨hr⟩ := OwnerRefinementProof.prefixExpansion S f τ base extras copies hp hc
  exact (RefinementSubstitutionSupport.endpoints hr).2
end LogicLineages.PersistentMarking.TargetExtrasListSupport
