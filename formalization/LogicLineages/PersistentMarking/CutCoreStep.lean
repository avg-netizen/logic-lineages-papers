import LogicLineages.PersistentMarking.CutLeftCoreProof
import LogicLineages.PersistentMarking.CutOwnerStep
namespace LogicLineages.PersistentMarking.CutCoreProof
open Spine NameBridge ExtendedMeasure

theorem step : CutCoreTargets.Step := by
  intro S n below s t u left right hc small ho
  cases left with
  | var => cases right; exact ⟨.var⟩
  | @abs σ s τ t x hp ht hxs hxt child =>
    exact CutLeftCoreProof.abstraction S n below σ τ s t u x hp ht hxs hxt child right hc ho
  | funHead hp ht heq htype matching =>
    exact CutLeftCoreProof.functionalHead S n below _ _ _ _ u hp ht heq htype matching right hc ho
  | put hp ht child =>
    obtain ⟨hcut⟩ := small _ child (by change treeSize child < 1 + treeSize child; omega) ho
    exact ⟨.put hp (CutEdgeProof.rightPaper ⟨right⟩ ht) hcut⟩
  | select hp ht ha harg hcall child =>
    obtain ⟨hcut⟩ := small _ child (by change treeSize child < 1 + treeSize child; omega) ho
    exact ⟨.select hp (CutEdgeProof.rightPaper ⟨right⟩ ht) ha harg hcall hcut⟩
  | @fabs f σ τ base extras body x hp ht hxs hxt child =>
    exact CutLeftCoreProof.functional S n below f σ τ base extras body u x hp ht hxs hxt child right hc ho
  | copy hp ht hprec whole =>
    exact CutLeftCoreProof.copyHead S n below _ _ _ _ _ u hp ht hprec whole right hc ho
  | stat hp ht heq multi whole =>
    exact CutLeftCoreProof.statHead S n below _ _ _ _ _ u hp ht heq multi whole right hc ho
  | inHead hp ht heq matching ordered =>
    exact CutOwnerStep.owner S n below _ _ _ _ _ _ _ u (Or.inl ⟨heq,⟨matching⟩,⟨ordered⟩⟩) hp ht right hc ho
  | marked1 hp ht hprec base extras =>
    exact CutOwnerStep.owner S n below _ _ _ _ _ _ _ u (Or.inr (Or.inl ⟨hprec,⟨base⟩,⟨extras⟩⟩)) hp ht right hc ho
  | marked2 hp ht heq multi base extras =>
    exact CutOwnerStep.owner S n below _ _ _ _ _ _ _ u (Or.inr (Or.inr ⟨heq,⟨multi⟩,⟨base⟩,⟨extras⟩⟩)) hp ht right hc ho
  | drop hp ht child =>
    obtain ⟨hcut⟩ := small _ child (by change treeSize child < 1 + treeSize child; omega) ho
    exact ⟨.drop hp (CutEdgeProof.rightPaper ⟨right⟩ ht) hcut⟩
  | perm hp ht hperm child =>
    obtain ⟨hcut⟩ := small _ child (by change treeSize child < 1 + treeSize child; omega) ho
    exact ⟨.perm hp (CutEdgeProof.rightPaper ⟨right⟩ ht) hperm hcut⟩
  | copies hp ht hcopies child =>
    obtain ⟨hcut⟩ := small _ child (by change treeSize child < 1 + treeSize child; omega) ho
    exact ⟨.copies hp (CutEdgeProof.rightPaper ⟨right⟩ ht) hcopies hcut⟩
  | pselect hp ht ha harg htuple hcall child =>
    obtain ⟨hcut⟩ := small _ child (by change treeSize child < 1 + treeSize child; omega) ho
    exact ⟨.pselect hp (CutEdgeProof.rightPaper ⟨right⟩ ht) ha harg htuple hcall hcut⟩
end LogicLineages.PersistentMarking.CutCoreProof
