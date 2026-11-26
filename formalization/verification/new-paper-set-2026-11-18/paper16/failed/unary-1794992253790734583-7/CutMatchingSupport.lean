import LogicLineages.PersistentMarking.CutOccurrenceTargets
namespace LogicLineages.PersistentMarking.CutMatchingSupport
open Spine ExtendedMeasure

theorem removeSwap {xs rest final : Args} {a b : Expr}
    (ha : Remove xs a rest) (hb : Remove rest b final) :
    ∃ mid, Remove xs b mid ∧ Remove mid a final := by
  induction ha generalizing final with
  | here => exact ⟨.cons _ final,.there hb,.here⟩
  | there ha ih =>
    cases hb with
    | here => exact ⟨_,.here,ha⟩
    | there hb =>
      obtain ⟨mid,hm,hn⟩ := ih hb
      exact ⟨.cons _ mid,.there hm,.there hn⟩

theorem removeOrdinaryParts {xs rest : Args} {x : Expr} (h : Remove xs x rest)
    (ho : OrdinaryArgs xs) : Ordinary x ∧ OrdinaryArgs rest := by
  induction h with
  | here => exact ho
  | there hr ih =>
    have hh := ih ho.2
    exact ⟨hh.1,ho.1,hh.2⟩

/-- Extract the actual source occurrence from a matching, retaining both its
edge and the entire remaining matching with strict original-tree bounds. -/
theorem extract {S : Signature} {xs ys rest : Args} {x : Expr}
    (hr : Remove xs x rest) (h : ExtendedMatchingTree S xs ys) :
    ∃ y tail, ∃ edge : ExtendedWeakTree S x y, Remove ys y tail ∧ treeSize edge < treeSize h ∧
      ∃ remaining : ExtendedMatchingTree S rest tail, treeSize remaining < treeSize h := by
  induction hr generalizing ys with
  | here =>
    cases h with
    | matchingCons hr edge remaining =>
      exact ⟨_,_,edge,hr,by simp only [treeSize]; omega,remaining,by simp only [treeSize]; omega⟩
  | there hr ih =>
    cases h with
    | matchingCons hremove edge remainder =>
      obtain ⟨y,tail,found,hfound,hbound,remaining,hrest⟩ := ih remainder
      obtain ⟨mid,hmid,hkeep⟩ := removeSwap hremove hfound
      refine ⟨y,mid,found,hmid,?_,.matchingCons hkeep edge remaining,?_⟩
      · simp only [treeSize]; omega
      · simp only [treeSize]; omega
end LogicLineages.PersistentMarking.CutMatchingSupport
