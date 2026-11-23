module
public import LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginConsumptionTargets
import Init.Data.List.Erase
import Init.Data.List.Lemmas

public section
namespace LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginConsumptionProof
open NumberedWindowCertifiedOriginConsumptionTargets (ExactOriginConsumption)

/-- Consume one matching occurrence, preferring the left tape when both
sides contain the requested head. Cancellation leaves the same removed tape. -/
theorem exact_OriginConsumption : ExactOriginConsumption := by
  intro left right kept
  induction kept generalizing left right with
  | nil =>
    intro removed source
    change (left ++ right).Perm removed at source
    exact ⟨[], [], left, right, List.Perm.rfl, List.Perm.rfl,
      List.Perm.rfl, source.symm⟩
  | cons a kept ih =>
    intro removed source
    change (left ++ right).Perm (a :: (kept ++ removed)) at source
    have present : a ∈ left ++ right :=
      source.symm.mem_iff.mp List.mem_cons_self
    by_cases onLeft : a ∈ left
    · have extracted : left.Perm (a :: left.erase a) :=
        List.perm_cons_erase onLeft
      have whole : (left ++ right).Perm (a :: (left.erase a ++ right)) :=
        extracted.append_right right
      have rest : (left.erase a ++ right).Perm (kept ++ removed) :=
        (whole.symm.trans source).cons_inv
      obtain ⟨kl, kr, rl, rr, hl, hr, hk, hd⟩ :=
        ih (left.erase a) right removed rest
      exact ⟨a :: kl, kr, rl, rr, extracted.trans (hl.cons a), hr, hk.cons a, hd⟩
    · have onRight : a ∈ right :=
        (List.mem_append.mp present).resolve_left onLeft
      have extracted : right.Perm (a :: right.erase a) :=
        List.perm_cons_erase onRight
      have whole : (left ++ right).Perm (a :: (left ++ right.erase a)) :=
        (extracted.append_left left).trans List.perm_middle
      have rest : (left ++ right.erase a).Perm (kept ++ removed) :=
        (whole.symm.trans source).cons_inv
      obtain ⟨kl, kr, rl, rr, hl, hr, hk, hd⟩ :=
        ih left (right.erase a) removed rest
      have recombine : (a :: (kl ++ kr)).Perm (kl ++ a :: kr) :=
        List.perm_middle.symm
      exact ⟨kl, a :: kr, rl, rr, hl, extracted.trans (hr.cons a),
        (hk.cons a).trans recombine, hd⟩

#print axioms exact_OriginConsumption

end LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginConsumptionProof
