module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetPresentationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetPresentationProof
open DirectMultisetPresentation

theorem permutationInvariance : DirectMultisetPresentationTargets.PermutationInvariance := by
  intro α R source target source' target' hs ht
  constructor
  · rintro ⟨kept, removed, inserted, hsource, htarget, hnonempty, hdom⟩
    exact ⟨kept, removed, inserted, hs.symm.trans hsource, ht.symm.trans htarget, hnonempty, hdom⟩
  · rintro ⟨kept, removed, inserted, hsource, htarget, hnonempty, hdom⟩
    exact ⟨kept, removed, inserted, hs.trans hsource, ht.trans htarget, hnonempty, hdom⟩

theorem occurrenceWitnesses : DirectMultisetPresentationTargets.OccurrenceWitnesses := by
  intro α R removed inserted
  constructor
  · intro h
    induction inserted with
    | nil => exact ⟨[], rfl, .nil⟩
    | cons y rest ih =>
      obtain ⟨z, hz, hr⟩ := h y (by simp)
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hz
      obtain ⟨indices, hlen, hw⟩ := ih (fun t ht => h t (by simp [ht]))
      exact ⟨i::indices, by simp [hlen], .cons ⟨z,hi,hr⟩ hw⟩
  · rintro ⟨indices, hlen, hw⟩
    clear hlen
    induction hw with
    | nil => simp
    | @cons y i rest indices hhead htail ih =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · obtain ⟨z, hz, hr⟩ := hhead
        exact ⟨z, List.mem_iff_getElem?.mpr ⟨i,hz⟩,hr⟩
      · exact ih t ht

theorem multisetCalibration : DirectMultisetPresentationTargets.MultisetCalibration := by
  intro α R source target
  constructor
  · rintro ⟨kept,removed,inserted,hs,ht,hn,hd⟩
    refine ⟨(kept : Multiset α),(removed : Multiset α),(inserted : Multiset α),?_,?_,?_,?_⟩
    · simpa only [Multiset.coe_add, Multiset.coe_eq_coe] using hs
    · simpa only [Multiset.coe_add, Multiset.coe_eq_coe] using ht
    · intro hzero
      exact hn ((Multiset.coe_eq_zero removed).mp hzero)
    · simpa only [Multiset.mem_coe] using hd
  · rintro ⟨kept,removed,inserted,hs,ht,hn,hd⟩
    obtain ⟨kept,rfl⟩ := Quotient.exists_rep kept
    obtain ⟨removed,rfl⟩ := Quotient.exists_rep removed
    obtain ⟨inserted,rfl⟩ := Quotient.exists_rep inserted
    refine ⟨kept,removed,inserted,?_,?_,?_,?_⟩
    · simpa only [Multiset.quot_mk_to_coe, Multiset.coe_add, Multiset.coe_eq_coe] using hs
    · simpa only [Multiset.quot_mk_to_coe, Multiset.coe_add, Multiset.coe_eq_coe] using ht
    · intro hnil
      apply hn
      exact (Multiset.coe_eq_zero removed).mpr hnil
    · simpa only [Multiset.quot_mk_to_coe, Multiset.mem_coe] using hd

theorem orderedLibraryCalibration : DirectMultisetPresentationTargets.OrderedLibraryCalibration := by
  intro α inst R hR source target
  rw [multisetCalibration]
  constructor
  · rintro ⟨kept,removed,inserted,hs,ht,hn,hd⟩
    exact ⟨kept,inserted,removed,hn,ht,hs,fun y hy => by
      obtain ⟨z,hz,hr⟩ := hd y hy
      exact ⟨z,hz,(hR z y).mp hr⟩⟩
  · rintro ⟨kept,inserted,removed,hn,ht,hs,hd⟩
    exact ⟨kept,removed,inserted,hs,ht,hn,fun y hy => by
      obtain ⟨z,hz,hr⟩ := hd y hy
      exact ⟨z,hz,(hR z y).mpr hr⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetPresentationProof
