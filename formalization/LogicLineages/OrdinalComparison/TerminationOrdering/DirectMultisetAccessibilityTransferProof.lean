module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibilityTransferTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibilityTransferProof
open DirectMultisetAccessibleSubtype DirectMultisetAccessibility

theorem accessibleSubtypeAccessibility :
    DirectMultisetAccessibilityTransferTargets.AccessibleSubtypeAccessibility := by
  intro α R a
  exact InvImage.accessible Subtype.val a.property

theorem eraseAccessible {α : Type} (R : α → α → Prop)
    (source : List (AccessibleElement R))
    (h : Acc (ReverseDirect (LiftedRelation R)) source) :
    Acc (ReverseDirect R) (source.map Subtype.val) := by
  induction h with
  | intro source h ih =>
    refine Acc.intro _ ?_
    intro target hd
    have hmembers : MembersAccessible R (source.map Subtype.val) := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact b.property
    have ht := DirectMultisetAccessibleSubtypeProof.directMemberClosure α R
      (source.map Subtype.val) target hmembers hd
    obtain ⟨lifted, he⟩ := DirectMultisetAccessibleSubtypeProof.occurrencePreservingLift α R target ht
    have hedge : ReverseDirect (LiftedRelation R) lifted source := by
      apply (DirectMultisetAccessibleSubtypeProof.exactLiftedDirect α R source lifted).mpr
      exact he.symm ▸ hd
    exact he ▸ ih lifted hedge

theorem memberAccessibilityTransfer :
    DirectMultisetAccessibilityTransferTargets.MemberAccessibilityTransfer := by
  intro α R source hm
  obtain ⟨lifted, he⟩ := DirectMultisetAccessibleSubtypeProof.occurrencePreservingLift α R source hm
  have hw : WellFounded (fun successor source : AccessibleElement R =>
      LiftedRelation R source successor) := ⟨accessibleSubtypeAccessibility α R⟩
  have hirr : ∀ a : AccessibleElement R, ¬ LiftedRelation R a a := hw.irrefl.irrefl
  have hl : Acc (ReverseDirect (LiftedRelation R)) lifted :=
    DirectMultisetAccessibilityProof.irreflexiveMemberAccessibility
      (AccessibleElement R) (LiftedRelation R) hirr lifted
      (fun a _ => accessibleSubtypeAccessibility α R a)
  exact he ▸ eraseAccessible R lifted hl

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibilityTransferProof
