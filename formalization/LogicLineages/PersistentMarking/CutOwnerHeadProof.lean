import LogicLineages.PersistentMarking.CutCoreSupport
namespace LogicLineages.PersistentMarking.CutOwnerHeadProof
open Spine ExtendedMeasure CutCoreSupport

theorem copy (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f g h : Head) (sb se tb te us : Args)
    (root : CutOwnerSyntax.Root S f sb se g tb te)
    (hp : PaperTerm S (.marked f h.result sb se) h.result)
    (ht : PaperTerm S (.marked g h.result tb te) h.result) (hu : PaperTerm S (.head h us) h.result)
    (hprec : Precedes S g h) (right : ExtendedWholeTree S g tb te us)
    (hc : treeSize right < n) (ho : OrdinaryArgs us) :
    ExtendedWeak S (.marked f h.result sb se) (.head h us) := by
  obtain ⟨hw⟩ := wholeRebase S n below f g sb se tb te us h.result root hp ht right hc ho
  have hfh : Precedes S f h := by
    rcases root with ⟨heq,_,_⟩ | ⟨hfg,_,_⟩ | ⟨heq,_,_,_⟩
    · exact equivPrecede heq hprec
    · exact precedeTrans hfg hprec
    · exact equivPrecede heq hprec
  exact ⟨.copy hp hu hfh hw⟩

theorem stat (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (f g h : Head) (sb se tb te us : Args)
    (root : CutOwnerSyntax.Root S f sb se g tb te)
    (hp : PaperTerm S (.marked f h.result sb se) h.result)
    (ht : PaperTerm S (.marked g h.result tb te) h.result) (hu : PaperTerm S (.head h us) h.result)
    (heq : Equivalent S g h) (right : ExtendedMultisetTree S tb us) (whole : ExtendedWholeTree S g tb te us)
    (hc : treeSize right < n) (hwc : treeSize whole < n) (ho : OrdinaryArgs us) :
    ExtendedWeak S (.marked f h.result sb se) (.head h us) := by
  obtain ⟨hw⟩ := wholeRebase S n below f g sb se tb te us h.result root hp ht whole hwc ho
  rcases root with ⟨hfg,⟨hm⟩,_⟩ | ⟨hfg,_,_⟩ | ⟨hfg,⟨hm⟩,_,_⟩
  · obtain ⟨hcomp⟩ := CutWeakStrictProof.weakStrict S n below sb tb us ⟨hm⟩ right hc ho
    exact ⟨.stat hp hu (equivTrans hfg heq) hcomp hw⟩
  · exact ⟨.copy hp hu (precedeEquiv hfg heq) hw⟩
  · obtain ⟨hcomp⟩ := CutStrictStrictProof.strictStrict S n below sb tb us ⟨hm⟩ right hc ho
    exact ⟨.stat hp hu (equivTrans hfg heq) hcomp hw⟩
end LogicLineages.PersistentMarking.CutOwnerHeadProof
