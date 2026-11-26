import LogicLineages.PersistentMarking.CutRemoveSupport
namespace LogicLineages.PersistentMarking.CutMatchingSupport
open Spine ExtendedMeasure CutRemoveSupport

/-- Actual source-occurrence extraction, with both remaining tree and edge
bounded strictly by the original matching count. -/
theorem extract {S : Signature} {xs ys rest : Args} {x : Expr}
    (hr : Remove xs x rest) (h : ExtendedMatchingTree S xs ys) :
    ∃ y tail, ∃ edge : ExtendedWeakTree S x y, Remove ys y tail ∧ treeSize edge < treeSize h ∧
      ∃ remaining : ExtendedMatchingTree S rest tail, treeSize remaining < treeSize h := by
  cases hr with
  | here =>
    cases h with
    | matchingCons hr edge remaining =>
      refine ⟨_,_,edge,hr,?_,remaining,?_⟩
      · change treeSize edge < 1 + treeSize edge + treeSize remaining
        omega
      · change treeSize remaining < 1 + treeSize edge + treeSize remaining
        omega
  | there hr =>
    cases h with
    | matchingCons hremove edge remainder =>
      obtain ⟨y,tail,found,hfound,hbound,remaining,hrest⟩ := extract hr remainder
      obtain ⟨mid,hmid,hkeep⟩ := removeSwap hremove hfound
      refine ⟨y,mid,found,hmid,?_,.matchingCons hkeep edge remaining,?_⟩
      · change treeSize found < 1 + treeSize edge + treeSize remainder
        omega
      · change 1 + treeSize edge + treeSize remaining < 1 + treeSize edge + treeSize remainder
        omega
termination_by sizeOf xs
end LogicLineages.PersistentMarking.CutMatchingSupport
