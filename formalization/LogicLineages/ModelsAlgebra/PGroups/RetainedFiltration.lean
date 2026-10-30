module
public import LogicLineages.ModelsAlgebra.PGroups.RetainedFiltrationTargets
public import LogicLineages.ModelsAlgebra.PGroups.CoherentTerminal
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTail
public import LogicLineages.ModelsAlgebra.PGroups.InternalProjection
public import LogicLineages.ModelsAlgebra.PGroups.QuotientHeight
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem retained_filtration_reflection : Targets.groupRetainedFiltrationReflection := by
  intro G _ p δ A K T hH hKT hA α x hx
  have hT : T ≤ (transfiniteFiltration p δ : AddSubgroup G) := by rw [hH]; exact le_sup_right
  by_cases hα : α ≤ δ
  · exact quotient_membership_reflection G p T δ hT α hα x
  have hδα : δ ≤ α := le_of_not_ge hα
  by_cases hxH : x ∈ (transfiniteFiltration p δ : AddSubgroup G)
  · have hxK : x ∈ K := by
      obtain ⟨a,ha,k,hk,rfl⟩ := AddSubgroup.mem_sup.mp hx
      have hkH : k ∈ (transfiniteFiltration p δ : AddSubgroup G) := by
        rw [hH]
        exact (le_sup_left : K ≤ K ⊔ T) hk
      have haH : a ∈ (transfiniteFiltration p δ : AddSubgroup G) := by
        simpa only [add_sub_cancel_right] using
          (transfiniteFiltration p δ : AddSubgroup G).sub_mem hxH hkH
      exact K.add_mem (hA ⟨ha,haH⟩) hk
    obtain ⟨e,he⟩ := coherent_terminal_quotient G p δ K T hH hKT
    let β := α - δ
    have hsum : δ+β = α := Ordinal.add_sub_cancel_of_le hδα
    have hG := transfinite_tail_membership G p δ β ⟨x,hxH⟩
    have hQ := transfinite_tail_membership (G ⧸ T) p δ β (e ⟨x,hxK⟩)
    have hK := internal_summand_filtration G K T (transfiniteFiltration p δ) hH hKT p β ⟨x,hxK⟩
    have heq := retraction_filtration_reflection K (transfiniteFiltration p δ : AddSubgroup (G ⧸ T))
      e.toAddMonoidHom e.symm.toAddMonoidHom e.symm_apply_apply p β ⟨x,hxK⟩
    rw [hsum] at hG hQ
    rw [he ⟨x,hxK⟩] at hQ
    exact hQ.symm.trans (heq.trans (hK.symm.trans hG))
  · constructor
    · intro hq
      have hqδ := transfiniteFiltration_antitone p hδα hq
      exact (hxH ((quotient_membership_reflection G p T δ hT δ le_rfl x).mp hqδ)).elim
    · intro hg
      exact (hxH (transfiniteFiltration_antitone p hδα hg)).elim

end LogicLineages.ModelsAlgebra.PGroups
