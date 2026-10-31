module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerAdjunctionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem digits_injective {H : Type} [AddCommGroup H] (p : ℕ) (hp : 0 < p)
    (a : H) (h k : H) (r s : ℤ) (hr : 0 ≤ r) (hrp : r < p)
    (hs : 0 ≤ s) (hsp : s < p)
    (he : walkerAdjunctionClass p a h r = walkerAdjunctionClass p a k s) :
    (h, r) = (k, s) := by
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (QuotientAddGroup.eq_iff_sub_mem.mp he)
  have hn₂ : n * (p : ℤ) = r - s := by
    simpa using congrArg Prod.snd hn
  have hm : r % (p : ℤ) = s % (p : ℤ) := by
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    rw [← hn₂]
    simp
  have hrs : r = s := by
    simpa only [Int.emod_eq_of_lt hr hrp, Int.emod_eq_of_lt hs hsp] using hm
  have hn0 : n = 0 := by
    have : n * (p : ℤ) = 0 := by simpa [hrs] using hn₂
    exact (mul_eq_zero.mp this).resolve_right (by omega)
  have hhk : h = k := by
    have hh := congrArg Prod.fst hn
    simpa [hn0, sub_eq_zero] using hh.symm
  exact Prod.ext hhk hrs

theorem walker_adjunction_unique_digits : Targets.walkerAdjunctionUniqueDigits := by
  intro H _ p hp a x
  obtain ⟨⟨h,z⟩, rfl⟩ := QuotientAddGroup.mk'_surjective (walkerAdjunctionRelations p a) x
  have hpz : (0 : ℤ) < p := by omega
  refine ⟨(h + (z / (p : ℤ)) • a, z % (p : ℤ)), ?_, ?_⟩
  · refine ⟨Int.emod_nonneg _ (ne_of_gt hpz), Int.emod_lt_of_pos _ hpz, ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨-(z / (p : ℤ)), ?_⟩
    apply Prod.ext
    · simp
    · change -(z / (p : ℤ)) * (p : ℤ) = z % (p : ℤ) - z
      simp only [neg_mul]
      have hz : z % (p : ℤ) + (z / (p : ℤ)) * (p : ℤ) = z := by
        simpa [mul_comm] using Int.emod_add_mul_ediv z (p : ℤ)
      omega
  · intro d hd
    apply digits_injective p hp a d.1 (h + (z / (p : ℤ)) • a) d.2 (z % (p : ℤ))
      hd.1 hd.2.1 (Int.emod_nonneg _ (ne_of_gt hpz)) (Int.emod_lt_of_pos _ hpz)
    exact hd.2.2.trans (by
      apply Eq.symm
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      apply AddSubgroup.mem_zmultiples_iff.mpr
      refine ⟨-(z / (p : ℤ)), ?_⟩
      apply Prod.ext
      · simp
      · change -(z / (p : ℤ)) * (p : ℤ) = z % (p : ℤ) - z
        simp only [neg_mul]
        have hz : z % (p : ℤ) + (z / (p : ℤ)) * (p : ℤ) = z := by
          simpa [mul_comm] using Int.emod_add_mul_ediv z (p : ℤ)
        omega)

theorem walker_adjunction_faithful : Targets.walkerAdjunctionFaithful := by
  intro H _ p hp a h k he
  exact congrArg Prod.fst (digits_injective p hp a h k 0 0 (by omega) (by omega)
    (by omega) (by omega) he)

theorem walker_adjunction_root_relation : Targets.walkerAdjunctionRootRelation := by
  intro H _ p a
  change (p • (QuotientAddGroup.mk' (walkerAdjunctionRelations p a)) (0,1)) = _
  rw [← map_nsmul]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply AddSubgroup.mem_zmultiples_iff.mpr
  exact ⟨1, by simp⟩

end LogicLineages.ModelsAlgebra.PGroups
