import LogicLineages.PersistentMarking.NumberedWindowHeadEnumerationCandidatesProof

namespace LogicLineages.PersistentMarking.NumberedWindowHeadEnumerationProof
open NumberedWindowDomain NumberedWindowHeadEnumerationTargets

private theorem rankBit (S : Spine.Signature) (f : Head) :
    (Spine.classRank S f).isSome = true ↔ Spine.Admitted S f := by
  cases h : Spine.classRank S f <;> simp [Spine.Admitted,h]

theorem bit (S : Spine.Signature) (K : List Ty) (f : Head) :
    headBit S K f = true ↔ HeadInWindow S K f := by
  simp only [headBit,Bool.and_eq_true,rankBit,List.all_eq_true,decide_eq_true_eq,HeadInWindow]

private theorem memUnique (f : Head) (fs : List Head) : f ∈ unique fs ↔ f ∈ fs := by
  induction fs with
  | nil => rfl
  | cons g gs ih =>
    rw [unique]
    split
    · rename_i h
      exact ih.trans ⟨List.mem_cons_of_mem _,fun hf =>
        (List.mem_cons.mp hf).elim (fun e => e.symm ▸ h) id⟩
    · simp only [List.mem_cons,ih]

private theorem uniqueNodup (fs : List Head) : (unique fs).Nodup := by
  induction fs with
  | nil => exact List.nodup_nil
  | cons g gs ih =>
    rw [unique]
    split
    · exact ih
    · rename_i h
      exact List.nodup_cons.mpr ⟨fun hg => h ((memUnique g gs).mp hg),ih⟩

theorem admitted : AdmittedHeadEnumeration := by
  intro S K
  refine ⟨uniqueNodup _,fun f => ?_⟩
  simp only [admittedHeads,memUnique,List.mem_filter,bit]
  exact ⟨And.right,fun h => ⟨NumberedWindowHeadEnumerationCandidatesProof.candidate h,h⟩⟩

theorem equivalent : EquivalentHeadEnumeration := by
  intro S K f
  obtain ⟨hn,hadmit⟩ := admitted S K
  refine ⟨List.filter_sublist.nodup hn,fun g => ?_⟩
  simp only [equivalentHeads,List.mem_filter,hadmit,decide_eq_true_eq]
  constructor
  · rintro ⟨hg,he⟩
    obtain ⟨n,hr⟩ := hg.1
    exact ⟨hg,n,he.trans hr,hr⟩
  · rintro ⟨hg,n,hf,hr⟩
    exact ⟨hg,hf.trans hr.symm⟩

end LogicLineages.PersistentMarking.NumberedWindowHeadEnumerationProof
