module

public import LogicLineages.ModelsAlgebra.PGroups.CircleTorsionTargets

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem circle_torsion_range : Targets.groupCircleTorsionRange := by
  intro n _
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    change n • ZMod.toAddCircle w = 0
    rw [← map_nsmul]
    have hw : n • w = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hw, map_zero]
  · intro hz
    change n • z = 0 at hz
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective z
    have hr : n • r ∈ AddSubgroup.zmultiples (1 : ℝ) := by
      apply (QuotientAddGroup.eq_zero_iff (n • r)).mp
      simpa only [QuotientAddGroup.mk_nsmul] using hz
    obtain ⟨a, ha⟩ := hr
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
    have he : r = (a : ℝ) / n := by
      apply (eq_div_iff hn).mpr
      simpa only [zsmul_eq_mul, nsmul_eq_mul, mul_one, mul_comm] using ha.symm
    refine ⟨(a : ZMod n), ?_⟩
    rw [ZMod.toAddCircle_intCast, ← he]

theorem circle_torsion_isomorphism : Targets.groupCircleTorsionIsomorphism := by
  intro n _
  let e := AddMonoidHom.ofInjective (ZMod.toAddCircle_injective n)
  rw [circle_torsion_range n] at e
  exact ⟨e⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
