module

public import LogicLineages.NativeModule.PersistentMarking.CutMatchingSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.CutMatchingProof
open Spine ExtendedMeasure

theorem compose (S : Signature) (n : Nat) (below : CutEdgeTargets.Below S n)
    (xs ys zs : Args) (left : ExtendedMatchingTree S xs ys) (right : ExtendedMatchingTree S ys zs)
    (hcount : treeSize right < n) (ho : OrdinaryArgs zs) :
    _root_.Nonempty (ExtendedMatchingTree S xs zs) := by
  cases xs with
  | nil => cases left; cases right; exact ⟨.matchingNil⟩
  | cons x xs =>
    cases left with
    | matchingCons hr edge rest =>
      obtain ⟨z,tail,rightEdge,hremove,hbound,rightRest,hrest⟩ := CutMatchingSupport.extract hr right
      have hord := CutRemoveSupport.removeOrdinaryParts hremove ho
      obtain ⟨hcomp⟩ := below x _ z rightEdge (by omega) hord.1 ⟨edge⟩
      obtain ⟨hcompRest⟩ := compose S n below xs _ tail rest rightRest (by omega) hord.2
      exact ⟨.matchingCons hremove hcomp hcompRest⟩
termination_by sizeOf xs

theorem weakWeak : CutOccurrenceTargets.WeakWeak := by
  intro S n below xs ys zs hl right hc ho
  obtain ⟨left⟩ := hl
  exact compose S n below xs ys zs left right hc ho
end LogicLineages.PersistentMarking.CutMatchingProof
