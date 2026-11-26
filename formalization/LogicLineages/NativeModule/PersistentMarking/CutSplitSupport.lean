module

public import LogicLineages.NativeModule.PersistentMarking.CutOccurrenceTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.CutSplitSupport
open Spine

theorem align {xs a b c d : Args} (h : Split xs a b) (k : Split xs c d) :
    ∃ ac ad bc bd, Split a ac ad ∧ Split b bc bd ∧ Split c ac bc ∧ Split d ad bd := by
  induction h generalizing c d with
  | nil => cases k; exact ⟨.nil,.nil,.nil,.nil,.nil,.nil,.nil,.nil⟩
  | left h ih =>
    cases k with
    | left k =>
      obtain ⟨ac,ad,bc,bd,ha,hb,hc,hd⟩ := ih k
      exact ⟨.cons _ ac,ad,bc,bd,.left ha,hb,.left hc,hd⟩
    | right k =>
      obtain ⟨ac,ad,bc,bd,ha,hb,hc,hd⟩ := ih k
      exact ⟨ac,.cons _ ad,bc,bd,.right ha,hb,hc,.left hd⟩
  | right h ih =>
    cases k with
    | left k =>
      obtain ⟨ac,ad,bc,bd,ha,hb,hc,hd⟩ := ih k
      exact ⟨ac,ad,.cons _ bc,bd,ha,.left hb,.right hc,hd⟩
    | right k =>
      obtain ⟨ac,ad,bc,bd,ha,hb,hc,hd⟩ := ih k
      exact ⟨ac,ad,bc,.cons _ bd,ha,.right hb,hc,.right hd⟩

theorem associate {xs a b c d : Args} (h : Split xs a b) (k : Split a c d) :
    ∃ rest, Split xs c rest ∧ Split rest d b := by
  induction h generalizing c d with
  | nil => cases k; exact ⟨.nil,.nil,.nil⟩
  | left h ih =>
    cases k with
    | left k =>
      obtain ⟨rest,hs,hr⟩ := ih k
      exact ⟨rest,.left hs,hr⟩
    | right k =>
      obtain ⟨rest,hs,hr⟩ := ih k
      exact ⟨.cons _ rest,.right hs,.left hr⟩
  | right h ih =>
    obtain ⟨rest,hs,hr⟩ := ih k
    exact ⟨.cons _ rest,.right hs,.right hr⟩

theorem leftAt {xs a b : Args} {i : Nat} {q : Expr} (h : Split xs a b) (ha : At a i q) :
    ∃ j, At xs j q := by
  induction h generalizing i with
  | nil => cases ha
  | left h ih =>
    cases ha with
    | here => exact ⟨0,.here⟩
    | there ha => obtain ⟨j,hj⟩ := ih ha; exact ⟨j+1,.there hj⟩
  | right h ih => obtain ⟨j,hj⟩ := ih ha; exact ⟨j+1,.there hj⟩

theorem rightAt {xs a b : Args} {i : Nat} {q : Expr} (h : Split xs a b) (ha : At b i q) :
    ∃ j, At xs j q := by
  induction h generalizing i with
  | nil => cases ha
  | left h ih => obtain ⟨j,hj⟩ := ih ha; exact ⟨j+1,.there hj⟩
  | right h ih =>
    cases ha with
    | here => exact ⟨0,.here⟩
    | there ha => obtain ⟨j,hj⟩ := ih ha; exact ⟨j+1,.there hj⟩

theorem atSides {xs a b : Args} {i : Nat} {q : Expr} (h : Split xs a b) (ha : At xs i q) :
    (∃ j, At a j q) ∨ (∃ j, At b j q) := by
  induction h generalizing i with
  | nil => cases ha
  | left h ih =>
    cases ha with
    | here => exact Or.inl ⟨0,.here⟩
    | there ha =>
      rcases ih ha with ⟨j,hj⟩ | ⟨j,hj⟩
      · exact Or.inl ⟨j+1,.there hj⟩
      · exact Or.inr ⟨j,hj⟩
  | right h ih =>
    cases ha with
    | here => exact Or.inr ⟨0,.here⟩
    | there ha =>
      rcases ih ha with ⟨j,hj⟩ | ⟨j,hj⟩
      · exact Or.inl ⟨j,hj⟩
      · exact Or.inr ⟨j+1,.there hj⟩

theorem nonemptyRight {xs a b : Args} (h : Split xs a b) (hb : Spine.Nonempty b) : Spine.Nonempty xs := by
  cases xs with
  | nil => cases h; exact hb
  | cons _ _ => trivial
end LogicLineages.PersistentMarking.CutSplitSupport
