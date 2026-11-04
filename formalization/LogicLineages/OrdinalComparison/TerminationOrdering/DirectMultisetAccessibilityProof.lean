module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibilityProof
open DirectMultisetAccessibility DirectMultisetCutPath

theorem positivePathTransGen : DirectMultisetAccessibilityTargets.PositivePathTransGen := by
  intro α R k source target hk hp
  revert hk
  induction hp with
  | refl source => intro hk; omega
  | @cons k source middle target hcut htail ih =>
    intro hk
    cases k with
    | zero =>
      cases htail
      exact .single hcut
    | succ k => exact (ih (Nat.zero_lt_succ k)).tail hcut

theorem irreflexiveMemberAccessibility :
    DirectMultisetAccessibilityTargets.IrreflexiveMemberAccessibility := by
  intro α R hirr source hmembers
  let r : α → α → Prop := fun successor source => R source successor
  letI : Std.Irrefl r := ⟨hirr⟩
  have hmulti : Acc (Relation.CutExpand r) (source : Multiset α) :=
    Relation.acc_of_singleton (fun a ha =>
      (hmembers a (Multiset.mem_coe.mp ha)).cutExpand)
  have hpull := InvImage.accessible (fun xs : List α => (xs : Multiset α)) hmulti.transGen
  apply Subrelation.accessible (r := InvImage (Relation.TransGen (Relation.CutExpand r))
    (fun xs : List α => (xs : Multiset α))) ?_ hpull
  intro target source h
  obtain ⟨k, hk, hp⟩ := DirectMultisetCutPathProof.directPositiveCutPath α R source target h
  exact positivePathTransGen α R k (source : Multiset α) (target : Multiset α) hk hp

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibilityProof
