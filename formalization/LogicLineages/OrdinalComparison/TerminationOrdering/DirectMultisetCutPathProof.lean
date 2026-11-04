module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetCutPathSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetCutPathProof
open DirectMultisetCutPath DirectMultisetPresentation DirectMultisetCutPathSupportProof

theorem singleOccurrenceCut : DirectMultisetCutPathTargets.ActualSingleOccurrenceCut := by
  intro α R kept inserted a h
  refine ⟨(inserted : Multiset α), a, ?_, ?_⟩
  · simpa only [Multiset.mem_coe] using h
  · simp [← Multiset.coe_add, add_assoc, add_comm, add_left_comm]

theorem dominatedOccurrencePath : DirectMultisetCutPathTargets.ActualDominatedOccurrencePath := by
  intro α R kept removed inserted h
  have hm : ∀ y ∈ (inserted : Multiset α), ∃ a ∈ removed, R a y := by
    simpa only [Multiset.mem_coe] using h
  simpa only [Multiset.coe_add] using
    dominatedMultisetPath R removed (kept : Multiset α) (inserted : Multiset α) hm

theorem directPositiveCutPath : DirectMultisetCutPathTargets.ActualDirectPositiveCutPath := by
  intro α R source target h
  obtain ⟨kept, removed, inserted, hs, ht, hn, hd⟩ := h
  refine ⟨removed.length, by cases removed with | nil => exact False.elim (hn rfl) | cons a rest => simp, ?_⟩
  have hp := dominatedOccurrencePath α R kept removed inserted hd
  rw [← Multiset.coe_eq_coe.mpr hs, ← Multiset.coe_eq_coe.mpr ht] at hp
  exact hp

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetCutPathProof
