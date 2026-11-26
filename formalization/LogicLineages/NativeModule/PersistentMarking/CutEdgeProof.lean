module

public import LogicLineages.NativeModule.PersistentMarking.CutEdgeTargets
public import LogicLineages.NativeModule.PersistentMarking.ExtendedMarkingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.CutEdgeProof
open Spine ExtendedMeasure

theorem leftPaper {S : Signature} {a b : Expr} {σ : Ty}
    (h : ExtendedWeak S a b) (hb : PaperTerm S b σ) : PaperTerm S a σ := by
  obtain ⟨h⟩ := h
  have hf := ExtendedEndpointProof.weakFacts h
  have ht : a.type = σ := hf.2.2.trans (SpineShiftProof.annotationExact _ _ _ hb.1)
  exact ht ▸ hf.1

theorem rightPaper {S : Signature} {a b : Expr} {σ : Ty}
    (h : ExtendedWeak S a b) (ha : PaperTerm S a σ) : PaperTerm S b σ := by
  obtain ⟨h⟩ := h
  have hf := ExtendedEndpointProof.weakFacts h
  have ht : b.type = σ := hf.2.2.symm.trans (SpineShiftProof.annotationExact _ _ _ ha.1)
  exact ht ▸ hf.2.1

theorem weakStrict : CutEdgeTargets.WeakStrict := by
  intro S n below a b c hab right hcount ho
  cases right with
  | @strictIntro b σ c marked hb hc hm child =>
    obtain ⟨a',hma⟩ := ExtendedMarkabilityProof.reflectMarkability S a b marked hab hm
    have hmarked := ExtendedMarkingProof.forward S a b hab
    rw [SpineMarkingProof.markHeadmark a a' hma,SpineMarkingProof.markHeadmark b marked hm] at hmarked
    have hchild : treeSize child < n := by
      change 1 + treeSize child < n at hcount
      omega
    obtain ⟨hout⟩ := below a' marked c child hchild ho hmarked
    exact ⟨.strictIntro (leftPaper hab hb) hc hma hout⟩

theorem strictWeak : CutEdgeTargets.StrictWeak := by
  intro S n below a b c hab right hcount ho
  obtain ⟨hab⟩ := hab
  cases hab with
  | @strictIntro a σ b marked ha hb hm child =>
    obtain ⟨hout⟩ := below marked b c right hcount ho ⟨child⟩
    exact ⟨.strictIntro ha (rightPaper ⟨right⟩ hb) hm hout⟩

theorem strictStrict : CutEdgeTargets.StrictStrict := by
  intro S n below a b c hab right hcount ho
  obtain ⟨hab⟩ := hab
  cases hab with
  | @strictIntro a σ b marked ha hb hm child =>
    cases right with
    | @strictIntro b τ c marked' hb' hc hm' rightChild =>
      have hmarked := ExtendedMarkingProof.forward S marked b ⟨child⟩
      have hfixed := SpineMarkingProof.markHeadmark marked marked (SpineMarkingProof.persistentSuccess a marked hm)
      rw [hfixed,SpineMarkingProof.markHeadmark b marked' hm'] at hmarked
      have hchild : treeSize rightChild < n := by
        change 1 + treeSize rightChild < n at hcount
        omega
      obtain ⟨hout⟩ := below marked marked' c rightChild hchild ho hmarked
      have heq : τ = σ := (SpineShiftProof.annotationExact _ _ _ hb'.1).symm.trans (SpineShiftProof.annotationExact _ _ _ hb.1)
      exact ⟨.strictIntro ha (heq ▸ hc) hm hout⟩

theorem fullEdges : CutEdgeTargets.FullEdges := ⟨weakStrict,strictWeak,strictStrict⟩
end LogicLineages.PersistentMarking.CutEdgeProof
