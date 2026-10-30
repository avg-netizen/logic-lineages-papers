module
public import LogicLineages.ModelsAlgebra.PGroups.CyclicSocleCoordinatesTargets
public import LogicLineages.ModelsAlgebra.PGroups.CyclicRoot
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem cyclic_socle_coordinate_injective : Targets.groupCyclicSocleCoordinateInjective := by
  intro p _ j
  let y : ZMod (p ^ (j+1)) := (p ^ j : ℕ)
  have hy : p • y = 0 := by
    simpa only [Nat.add_sub_cancel] using (power_cyclic_socle_witness p (j+1) (Nat.succ_pos j)).1
  have hn : y ≠ 0 := by
    simpa only [Nat.add_sub_cancel] using (power_cyclic_socle_witness p (j+1) (Nat.succ_pos j)).2
  have ho : addOrderOf y = p := by
    simpa only [Nat.zero_add, pow_one] using cyclic_root_order p (ZMod (p ^ (j+1))) 0 y
      (by simpa only [Nat.zero_add, pow_one] using hy) (by simpa only [pow_zero, one_smul] using hn)
  unfold cyclicSocleCoordinate cyclicRootHom
  apply (ZMod.lift_injective p).mpr
  intro a ha
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr
  rw [← ho]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr ha

theorem cyclic_socle_coordinate_range : Targets.groupCyclicSocleCoordinateRange := by
  intro p _ j
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    change p • cyclicSocleCoordinate p j a = 0
    rw [← map_nsmul]
    have ha : p • a = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [ha, map_zero]
  · intro hz
    obtain ⟨w,hw⟩ := power_cyclic_socle_roots p (j+1) (Nat.succ_pos j) z hz
    simp only [Nat.add_sub_cancel] at hw
    obtain ⟨a,rfl⟩ := ZMod.intCast_surjective w
    refine ⟨(a : ZMod p), ?_⟩
    unfold cyclicSocleCoordinate
    rw [cyclic_root_evaluation]
    simpa only [zsmul_eq_mul, nsmul_eq_mul, mul_comm] using hw

theorem cyclic_socle_root_composition : Targets.groupCyclicSocleRootComposition := by
  intro p _ G _ j y hy a
  have hk : p • ((p ^ j : ℕ) : ZMod (p ^ (j+1))) = 0 := by
    simpa only [Nat.add_sub_cancel] using (power_cyclic_socle_witness p (j+1) (Nat.succ_pos j)).1
  have hc : cyclicSocleCoordinate p j a = a.val • ((p ^ j : ℕ) : ZMod (p ^ (j+1))) := by
    have he := cyclic_root_evaluation p (ZMod (p ^ (j+1))) ((p ^ j : ℕ) : ZMod (p ^ (j+1))) hk (a.val : ℤ)
    simpa only [cyclicSocleCoordinate, Int.cast_natCast, natCast_zsmul, ZMod.natCast_zmod_val] using he
  rw [hc, map_nsmul]
  have hgen : cyclicRootHom (p ^ (j+1)) G y hy ((p ^ j : ℕ) : ZMod (p ^ (j+1))) = p ^ j • y := by
    simpa only [Int.cast_natCast, natCast_zsmul] using
      cyclic_root_evaluation (p ^ (j+1)) G y hy ((p ^ j : ℕ) : ℤ)
  rw [hgen]

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
