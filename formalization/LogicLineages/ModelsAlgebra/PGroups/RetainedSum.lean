module
public import LogicLineages.ModelsAlgebra.PGroups.RetainedSumTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem retained_sum_disjoint : Targets.groupRetainedSumDisjoint := by
  intro G _ A K T H hH hKT hA
  apply AddSubgroup.disjoint_def.mpr
  intro x hx ht
  obtain ⟨a,ha,k,hk,rfl⟩ := AddSubgroup.mem_sup.mp hx
  have hkH : k ∈ H := by rw [hH]; exact (le_sup_left : K ≤ K ⊔ T) hk
  have hxH : a+k ∈ H := by rw [hH]; exact (le_sup_right : T ≤ K ⊔ T) ht
  have haH : a ∈ H := by simpa only [add_sub_cancel_right] using H.sub_mem hxH hkH
  exact AddSubgroup.disjoint_def.mp hKT (K.add_mem (hA ⟨ha,haH⟩) hk) ht

theorem retained_sum_quotient_injective : Targets.groupRetainedSumQuotientInjective := by
  intro G _ A K T H hH hKT hA x y he
  have ht : (x : G) - y ∈ T := QuotientAddGroup.eq_iff_sub_mem.mp he
  have hz : (x : G) - y = 0 := AddSubgroup.disjoint_def.mp
    (retained_sum_disjoint G A K T H hH hKT hA)
    ((A ⊔ K).sub_mem x.property y.property) ht
  exact Subtype.ext (sub_eq_zero.mp hz)

end LogicLineages.ModelsAlgebra.PGroups
