import LogicLineages.PersistentMarking.TargetExtrasListSupport
namespace LogicLineages.PersistentMarking.TargetExtrasRootSupport
open Spine TargetExtrasListSupport

inductive Change (f : Head) (base extras : Args) : Args → Prop where
  | «prefix» : Prefix pref extras → Change f base extras pref
  | perm : Permutation extras reordered → Change f base extras reordered
  | copies : PrefixCopies f base extras copies → Change f base extras (extras.append copies)

theorem changedPaper {S : Signature} {f : Head} {τ : Ty} {base extras changed : Args}
    (hp : PaperTerm S (.marked f τ base extras) τ) (h : Change f base extras changed) :
    PaperTerm S (.marked f τ base changed) τ := by
  cases h with
  | «prefix» h => exact prefixPaper hp h
  | perm h => exact permutationPaper hp h
  | copies h => exact copiesPaper hp h

theorem changedPaperAt {S : Signature} {f : Head} {τ ρ : Ty} {base extras changed : Args}
    (hp : PaperTerm S (.marked f ρ base extras) τ) (h : Change f base extras changed) :
    PaperTerm S (.marked f ρ base changed) τ := by
  have he := SpineShiftProof.annotationExact _ _ _ hp.1
  change ρ = τ at he
  subst τ
  exact changedPaper hp h

theorem inCopies {S : Signature} {f g : Head} {τ : Ty} {sb se tb te cs : Args}
    (hp : PaperTerm S (.marked f τ sb se) τ) (ht : PaperTerm S (.marked g τ tb te) τ)
    (heq : Equivalent S f g) (hb : ExtendedMatchingTree S sb tb)
    (he : ExtendedOrderedTree S se te) (hc : PrefixCopies g tb te cs) :
    ∃ ds, PrefixCopies f sb se ds ∧ _root_.Nonempty (ExtendedOrderedTree S ds cs) := by
  induction hc with
  | nil => exact ⟨.nil,.nil,⟨.orderedNil⟩⟩
  | @cons q qs hcopy hrest ih =>
    generalize hσ : q.type = output at hcopy
    cases hcopy with
    | @intro pref ρ hprefix =>
      obtain ⟨source,hsp,⟨hordered⟩⟩ := orderedPrefix he hprefix
      obtain ⟨ds,hds,⟨horderedRest⟩⟩ := ih
      exact ⟨.cons (.marked f output sb source) ds,.cons (.intro hsp) hds,
        ⟨.orderedCons (.inHead (prefixPaper hp hsp) (prefixPaper ht hprefix) heq hb hordered) horderedRest⟩⟩

theorem inRoot {S : Signature} {f g : Head} {τ : Ty} {sb se tb te changed : Args}
    (hp : PaperTerm S (.marked f τ sb se) τ) (ht : PaperTerm S (.marked g τ tb te) τ)
    (heq : Equivalent S f g) (hb : ExtendedMatchingTree S sb tb)
    (he : ExtendedOrderedTree S se te) (hc : Change g tb te changed) :
    ExtendedWeak S (.marked f τ sb se) (.marked g τ tb changed) := by
  have ht' := changedPaper ht hc
  cases hc with
  | «prefix» hpre =>
    obtain ⟨source,hsp,⟨hordered⟩⟩ := orderedPrefix he hpre
    obtain ⟨tail,hse⟩ := prefixSuffix hsp
    have hroot := ExtendedTree.inHead (prefixPaper hp hsp) ht' heq hb hordered
    subst se
    exact ⟨.drop hp ht' hroot⟩
  | perm hperm =>
    obtain ⟨source,hsperm,⟨hordered⟩⟩ := orderedPermutation he hperm
    exact ⟨.perm hp ht' hsperm (.inHead (permutationPaper hp hsperm) ht' heq hb hordered)⟩
  | copies hcopies =>
    obtain ⟨ds,hds,⟨hordered⟩⟩ := inCopies hp ht heq hb he hcopies
    obtain ⟨hall⟩ := UnaryTransportSupport.appendOrdered he hordered
    exact ⟨.copies hp ht' hds (.inHead (copiesPaper hp hds) ht' heq hb hall)⟩

theorem marked1Copies {S : Signature} {f g : Head} {τ : Ty} {sb se tb te cs : Args}
    (hp : PaperTerm S (.marked f τ sb se) τ) (ht : PaperTerm S (.marked g τ tb te) τ)
    (hprec : Precedes S f g) (hb : ExtendedWholeTree S f sb se tb)
    (he : ExtendedWholeTree S f sb se te) (hc : PrefixCopies g tb te cs) :
    _root_.Nonempty (ExtendedWholeTree S f sb se cs) := by
  induction hc with
  | nil => exact ⟨.wholeNil⟩
  | @cons q qs hcopy hrest ih =>
    generalize hσ : q.type = output at hcopy
    cases hcopy with
    | @intro pref ρ hprefix =>
      obtain ⟨hpre⟩ := wholePrefix he hprefix
      obtain ⟨hrest'⟩ := ih
      exact ⟨.wholeCons (.marked1 (AuxiliaryReflexivityProof.retypePaper S f τ output sb se hp)
        (prefixPaper ht hprefix) hprec hb hpre) hrest'⟩

theorem marked2Copies {S : Signature} {f g : Head} {τ : Ty} {sb se tb te cs : Args}
    (hp : PaperTerm S (.marked f τ sb se) τ) (ht : PaperTerm S (.marked g τ tb te) τ)
    (heq : Equivalent S f g) (hm : ExtendedMultisetTree S sb tb) (hb : ExtendedWholeTree S f sb se tb)
    (he : ExtendedWholeTree S f sb se te) (hc : PrefixCopies g tb te cs) :
    _root_.Nonempty (ExtendedWholeTree S f sb se cs) := by
  induction hc with
  | nil => exact ⟨.wholeNil⟩
  | @cons q qs hcopy hrest ih =>
    generalize hσ : q.type = output at hcopy
    cases hcopy with
    | @intro pref ρ hprefix =>
      obtain ⟨hpre⟩ := wholePrefix he hprefix
      obtain ⟨hrest'⟩ := ih
      exact ⟨.wholeCons (.marked2 (AuxiliaryReflexivityProof.retypePaper S f τ output sb se hp)
        (prefixPaper ht hprefix) heq hm hb hpre) hrest'⟩

theorem marked1Root {S : Signature} {f g : Head} {τ : Ty} {sb se tb te changed : Args}
    (hp : PaperTerm S (.marked f τ sb se) τ) (ht : PaperTerm S (.marked g τ tb te) τ)
    (hprec : Precedes S f g) (hb : ExtendedWholeTree S f sb se tb)
    (he : ExtendedWholeTree S f sb se te) (hc : Change g tb te changed) :
    ExtendedWeak S (.marked f τ sb se) (.marked g τ tb changed) := by
  have ht' := changedPaper ht hc
  have hextras : _root_.Nonempty (ExtendedWholeTree S f sb se changed) := by
    cases hc with
    | «prefix» h => exact wholePrefix he h
    | perm h => exact wholePermutation he h
    | copies h =>
      obtain ⟨hnew⟩ := marked1Copies hp ht hprec hb he h
      exact UnaryTransportSupport.appendWhole he hnew
  obtain ⟨hextras⟩ := hextras
  exact ⟨.marked1 hp ht' hprec hb hextras⟩

theorem marked2Root {S : Signature} {f g : Head} {τ : Ty} {sb se tb te changed : Args}
    (hp : PaperTerm S (.marked f τ sb se) τ) (ht : PaperTerm S (.marked g τ tb te) τ)
    (heq : Equivalent S f g) (hm : ExtendedMultisetTree S sb tb) (hb : ExtendedWholeTree S f sb se tb)
    (he : ExtendedWholeTree S f sb se te) (hc : Change g tb te changed) :
    ExtendedWeak S (.marked f τ sb se) (.marked g τ tb changed) := by
  have ht' := changedPaper ht hc
  have hextras : _root_.Nonempty (ExtendedWholeTree S f sb se changed) := by
    cases hc with
    | «prefix» h => exact wholePrefix he h
    | perm h => exact wholePermutation he h
    | copies h =>
      obtain ⟨hnew⟩ := marked2Copies hp ht heq hm hb he h
      exact UnaryTransportSupport.appendWhole he hnew
  obtain ⟨hextras⟩ := hextras
  exact ⟨.marked2 hp ht' heq hm hb hextras⟩
end LogicLineages.PersistentMarking.TargetExtrasRootSupport
