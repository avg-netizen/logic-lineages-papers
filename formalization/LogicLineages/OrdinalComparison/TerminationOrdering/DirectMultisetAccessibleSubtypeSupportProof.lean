module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibleSubtypeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibleSubtypeSupportProof
open DirectMultisetAccessibleSubtype DirectMultisetPresentation

theorem liftList {α : Type} (R : α → α → Prop) (xs : List α)
    (h : MembersAccessible R xs) :
    ∃ lifted : List (AccessibleElement R), lifted.map Subtype.val = xs := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons a rest ih =>
    obtain ⟨tail, ht⟩ := ih (fun b hb => h b (by simp [hb]))
    exact ⟨⟨a, h a (by simp)⟩ :: tail, congrArg (List.cons a) ht⟩

theorem witnessAccessible {α : Type} (R : α → α → Prop)
    (source kept removed inserted : List α)
    (hsource : MembersAccessible R source) (hs : source.Perm (kept ++ removed))
    (hd : ∀ y ∈ inserted, ∃ a ∈ removed, R a y) :
    MembersAccessible R kept ∧ MembersAccessible R removed ∧ MembersAccessible R inserted := by
  have hk : MembersAccessible R kept := fun a ha =>
    hsource a (hs.mem_iff.mpr (List.mem_append.mpr (Or.inl ha)))
  have hr : MembersAccessible R removed := fun a ha =>
    hsource a (hs.mem_iff.mpr (List.mem_append.mpr (Or.inr ha)))
  refine ⟨hk, hr, ?_⟩
  intro y hy
  obtain ⟨a, ha, hrel⟩ := hd y hy
  exact (hr a ha).inv hrel

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibleSubtypeSupportProof
