module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationSupportProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitHFreeCoreProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationProof
open WholeBoundInitialization

theorem row_allowed (bound : List Nat) (r : NormalForm.Row)
    (hr : ∀ a ∈ r.2, (∃ i : Nat, a.2 = NormalForm.Summand.variable i) ∨
      (∃ i : Nat, a.2 = NormalForm.Summand.phi i 0)) :
    PlainMaximum.allowed bound (row bound r) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  rw [literalOccurrencePartition bound r] at ha
  obtain ⟨ha, hb⟩ := List.mem_filter.mp ha
  rcases hr a ha with ⟨i, hi⟩ | ⟨i, hi⟩
  · simpa only [PlainMaximum.allowedSummand, hi, NormalForm.Summand.name] using hb
  · simpa only [PlainMaximum.allowedSummand, hi, NormalForm.Summand.name,
      decide_true, Bool.and_true] using hb

theorem actualAllowedTest : WholeBoundInitializationTargets.ActualAllowedTest := by
  intro bound p
  induction p with
  | truth => intro h; rfl
  | falsity => intro h; rfl
  | atom a =>
      intro h
      have ha := h a (List.mem_singleton_self a)
      cases a <;> exact row_allowed bound _ ha
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      intro h
      apply Bool.and_eq_true_iff.mpr
      exact ⟨ihp (fun a ha => h a (List.mem_append_left _ ha)),
        ihq (fun a ha => h a (List.mem_append_right _ ha))⟩
  | disjunction p q ihp ihq =>
      intro h
      apply Bool.and_eq_true_iff.mpr
      exact ⟨ihp (fun a ha => h a (List.mem_append_left _ ha)),
        ihq (fun a ha => h a (List.mem_append_right _ ha))⟩

theorem entries_hfree (bound : List Nat) (positive negative : Term)
    (es : List (Int × NormalForm.Summand))
    (hp : PlainBlockSplit.termHFree positive = true)
    (hn : PlainBlockSplit.termHFree negative = true)
    (he : ∀ a ∈ es, PlainBlockSplit.summandHFree a.2 = true) :
    PlainBlockSplit.rowHFree (entries bound positive negative es) = true := by
  open PlainBlockSplit PlainBlockSplitProof in
  induction es with
  | nil => exact hfree_row_of_parts _ hp hn (by simp [entries])
  | cons a es ih =>
      have htail := ih (fun b hb => he b (List.mem_cons_of_mem a hb))
      have hparts := hfree_row_parts _ htail
      by_cases h : bound.contains a.2.name = true
      · simp only [entries, if_pos h]
        apply hfree_row_of_parts
        · exact hparts.1
        · exact hparts.2.1
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact he b List.mem_cons_self
          · exact hparts.2.2 b hb
      · have ht := hfree_summand_term a.2 (he a List.mem_cons_self)
        simp only [entries, if_neg h]
        apply hfree_row_of_parts
        · exact hfree_add _ _ ht hparts.1
        · exact hfree_add _ _ ht hparts.2.1
        · exact hparts.2.2

theorem row_hfree (bound : List Nat) (r : NormalForm.Row)
    (hr : ∀ a ∈ r.2, (∃ i : Nat, a.2 = NormalForm.Summand.variable i) ∨
      (∃ i : Nat, a.2 = NormalForm.Summand.phi i 0)) :
    PlainBlockSplit.rowHFree (row bound r) = true := by
  apply entries_hfree bound _ _ r.2 rfl rfl
  intro a ha
  rcases hr a ha with ⟨i, hi⟩ | ⟨i, hi⟩ <;>
    simp only [hi, PlainBlockSplit.summandHFree]

theorem hFreeInitialization : WholeBoundInitializationTargets.HFreeInitialization := by
  intro bound p
  induction p with
  | truth => intro h; rfl
  | falsity => intro h; rfl
  | atom a =>
      intro h
      have ha := h a (List.mem_singleton_self a)
      cases a <;> exact row_hfree bound _ ha
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      intro h
      apply Bool.and_eq_true_iff.mpr
      exact ⟨ihp (fun a ha => h a (List.mem_append_left _ ha)),
        ihq (fun a ha => h a (List.mem_append_right _ ha))⟩
  | disjunction p q ihp ihq =>
      intro h
      apply Bool.and_eq_true_iff.mpr
      exact ⟨ihp (fun a ha => h a (List.mem_append_left _ ha)),
        ihq (fun a ha => h a (List.mem_append_right _ ha))⟩

#print axioms row_allowed
#print axioms actualAllowedTest
#print axioms entries_hfree
#print axioms row_hfree
#print axioms hFreeInitialization
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationProof
