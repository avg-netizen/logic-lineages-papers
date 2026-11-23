module

public import LogicLineages.NativeModule.PersistentMarking.CutPartitionSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.CutSourcePartitionSupport
open Spine ExtendedMeasure

theorem restoreLeft {xs tail kept removed : Args} {q : Expr}
    (hr : Remove xs q tail) (hs : Split tail kept removed) :
    ∃ ks, Split xs ks removed ∧ Remove ks q kept := by
  induction hr generalizing kept removed with
  | here => exact ⟨.cons _ kept,.left hs,.here⟩
  | there hr ih =>
    cases hs with
    | left hs =>
      obtain ⟨ks,hsp,hrem⟩ := ih hs
      exact ⟨.cons _ ks,.left hsp,.there hrem⟩
    | right hs =>
      obtain ⟨ks,hsp,hrem⟩ := ih hs
      exact ⟨ks,.right hsp,hrem⟩

theorem restoreRight {xs tail kept removed : Args} {q : Expr}
    (hr : Remove xs q tail) (hs : Split tail kept removed) :
    ∃ rs, Split xs kept rs ∧ Remove rs q removed := by
  induction hr generalizing kept removed with
  | here => exact ⟨.cons _ removed,.right hs,.here⟩
  | there hr ih =>
    cases hs with
    | left hs =>
      obtain ⟨rs,hsp,hrem⟩ := ih hs
      exact ⟨rs,.left hsp,hrem⟩
    | right hs =>
      obtain ⟨rs,hsp,hrem⟩ := ih hs
      exact ⟨.cons _ rs,.right hsp,.there hrem⟩

/-- Project the right matching along an actual source partition. Both
constructed matching counts are bounded by the original matching count. -/
theorem matchingSourceSplit {S : Signature} {xs ys kept removed : Args}
    (hs : Split xs kept removed) (h : ExtendedMatchingTree S xs ys) :
    ∃ ks rs, Split ys ks rs ∧
      ∃ hk : ExtendedMatchingTree S kept ks, ∃ hr : ExtendedMatchingTree S removed rs,
        treeSize hk ≤ treeSize h ∧ treeSize hr ≤ treeSize h := by
  cases hs with
  | nil => cases h; exact ⟨.nil,.nil,.nil,.matchingNil,.matchingNil,Nat.le_refl _,Nat.le_refl _⟩
  | left hs =>
    cases h with
    | matchingCons hr edge tail =>
      obtain ⟨ks,rs,hsp,hk,hrm,hkb,hrb⟩ := matchingSourceSplit hs tail
      obtain ⟨ks',hsp',hrem⟩ := restoreLeft hr hsp
      refine ⟨ks',rs,hsp',.matchingCons hrem edge hk,hrm,?_,?_⟩
      · change 1 + treeSize edge + treeSize hk ≤ 1 + treeSize edge + treeSize tail
        omega
      · change treeSize hrm ≤ 1 + treeSize edge + treeSize tail
        omega
  | right hs =>
    cases h with
    | matchingCons hr edge tail =>
      obtain ⟨ks,rs,hsp,hk,hrm,hkb,hrb⟩ := matchingSourceSplit hs tail
      obtain ⟨rs',hsp',hrem⟩ := restoreRight hr hsp
      refine ⟨ks,rs',hsp',hk,.matchingCons hrem edge hrm,?_,?_⟩
      · change treeSize hk ≤ 1 + treeSize edge + treeSize tail
        omega
      · change 1 + treeSize edge + treeSize hrm ≤ 1 + treeSize edge + treeSize tail
        omega
termination_by sizeOf xs
end LogicLineages.PersistentMarking.CutSourcePartitionSupport
