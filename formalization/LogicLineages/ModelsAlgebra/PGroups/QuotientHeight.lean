module
public import LogicLineages.ModelsAlgebra.PGroups.QuotientHeightTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem quotient_membership_reflection : Targets.groupQuotientMembershipReflection := by
  intro G _ p T δ hT α hα x
  rw [quotient_filtration_below p T δ hT α hα]
  constructor
  · rintro ⟨y,hy,he⟩
    have ht : y-x ∈ T := QuotientAddGroup.eq_iff_sub_mem.mp he
    have hs : y-x ∈ (transfiniteFiltration p α : AddSubgroup G) :=
      transfiniteFiltration_antitone p hα (hT ht)
    simpa only [sub_sub_cancel] using (transfiniteFiltration p α : AddSubgroup G).sub_mem hy hs
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem quotient_successor_height_reflection : Targets.groupQuotientSuccessorHeightReflection := by
  intro G _ p T δ hT α hα x
  have hle : α ≤ δ := (le_of_lt (Order.lt_add_one_iff.mpr le_rfl)).trans hα
  rw [quotient_membership_reflection G p T δ hT α hle,
    quotient_membership_reflection G p T δ hT (α+1) hα]

end LogicLineages.ModelsAlgebra.PGroups
