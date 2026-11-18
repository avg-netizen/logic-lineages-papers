import LogicLineages.PersistentMarking.CutMatchingSupport
namespace LogicLineages.PersistentMarking.CutPartitionSupport
open Spine ExtendedMeasure

/-- Remove one original occurrence and identify its unique partition side. -/
theorem splitRemove {xs kept removed rest : Args} {q : Expr}
    (hs : Split xs kept removed) (hr : Remove xs q rest) :
    (∃ ks, Remove kept q ks ∧ Split rest ks removed) ∨
    (∃ rs, Remove removed q rs ∧ Split rest kept rs) := by
  induction hs generalizing rest with
  | nil => cases hr
  | left hs ih =>
    cases hr with
    | here => exact Or.inl ⟨_,.here,hs⟩
    | there hr =>
      rcases ih hr with ⟨ks,hk,hsp⟩ | ⟨rs,hr,hsp⟩
      · exact Or.inl ⟨.cons _ ks,.there hk,.left hsp⟩
      · exact Or.inr ⟨rs,hr,.left hsp⟩
  | right hs ih =>
    cases hr with
    | here => exact Or.inr ⟨_,.here,hs⟩
    | there hr =>
      rcases ih hr with ⟨ks,hk,hsp⟩ | ⟨rs,hr,hsp⟩
      · exact Or.inl ⟨ks,hk,.right hsp⟩
      · exact Or.inr ⟨.cons _ rs,.there hr,.right hsp⟩

/-- Pull a literal target partition back through a weak occurrence bijection. -/
theorem matchingTargetSplit {S : Signature} {xs ys kept removed : Args}
    (h : ExtendedMatchingTree S xs ys) (hs : Split ys kept removed) :
    ∃ ks rs, Split xs ks rs ∧ _root_.Nonempty (ExtendedMatchingTree S ks kept) ∧
      _root_.Nonempty (ExtendedMatchingTree S rs removed) := by
  cases xs with
  | nil => cases h; cases hs; exact ⟨.nil,.nil,.nil,⟨.matchingNil⟩,⟨.matchingNil⟩⟩
  | cons x xs =>
    cases h with
    | matchingCons hr edge rest =>
      rcases splitRemove hs hr with ⟨kept',hk,hsp⟩ | ⟨removed',hr,hsp⟩
      · obtain ⟨ks,rs,hs',⟨hkeep⟩,⟨hremove⟩⟩ := matchingTargetSplit rest hsp
        exact ⟨.cons x ks,rs,.left hs',⟨.matchingCons hk edge hkeep⟩,⟨hremove⟩⟩
      · obtain ⟨ks,rs,hs',⟨hkeep⟩,⟨hremove⟩⟩ := matchingTargetSplit rest hsp
        exact ⟨ks,.cons x rs,.right hs',⟨hkeep⟩,⟨.matchingCons hr edge hremove⟩⟩
termination_by sizeOf xs

theorem matchingNonempty {S : Signature} {xs ys : Args}
    (h : ExtendedMatchingTree S xs ys) (hy : Spine.Nonempty ys) : Spine.Nonempty xs := by
  cases xs with
  | nil => cases h; exact hy
  | cons _ _ => trivial
end LogicLineages.PersistentMarking.CutPartitionSupport
