module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferModelTargets
public import LogicLineages.ModelsAlgebra.PGroups.CountableReducedZeroProof
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem genuine_pruefer_model : Targets.genuinePrueferModel := by
  intro p _
  have hp : p.Prime := Fact.out
  have hpQ : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let q : ℚ →+ RationalModIntegers := QuotientAddGroup.mk' _
  have hprimary : ∀ x : PrueferModel p, ∃ k : ℕ, p^k • x = 0 := by
    intro x
    obtain ⟨k,hk⟩ := x.property
    exact ⟨k,Subtype.ext hk⟩
  have hsurj : ∀ x : PrueferModel p, ∃ y : PrueferModel p, p • y = x := by
    intro x
    obtain ⟨r,hr⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1:ℚ)) (x:RationalModIntegers)
    have hroot : p • q (r/(p:ℚ)) = (x:RationalModIntegers) := by
      rw [← map_nsmul]
      have he : p • (r/(p:ℚ)) = r := by
        rw [nsmul_eq_mul]
        field_simp
      rw [he]
      exact hr
    obtain ⟨k,hk⟩ := x.property
    have hymem : q (r/(p:ℚ)) ∈ PrueferModel p := by
      refine ⟨k+1,?_⟩
      rw [pow_succ, mul_comm (p^k) p, mul_nsmul, hroot]
      exact hk
    exact ⟨⟨q (r/(p:ℚ)),hymem⟩,Subtype.ext hroot⟩
  refine ⟨hprimary,p_primary_divisible_from_p_surjective (PrueferModel p) p hprimary hsurj,?_⟩
  have hpt : p • q (1/(p:ℚ)) = 0 := by
    rw [← map_nsmul]
    have he : p • (1/(p:ℚ)) = 1 := by
      rw [nsmul_eq_mul]
      field_simp
    rw [he]
    exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_zmultiples (1:ℚ))
  have htmem : q (1/(p:ℚ)) ∈ PrueferModel p := ⟨1,by simpa using hpt⟩
  refine ⟨⟨q (1/(p:ℚ)),htmem⟩,?_,Subtype.ext hpt⟩
  intro he
  have hz : q (1/(p:ℚ)) = 0 := congrArg Subtype.val he
  obtain ⟨z,hz⟩ := AddSubgroup.mem_zmultiples_iff.mp ((QuotientAddGroup.eq_zero_iff _).mp hz)
  have hz' : (z:ℚ) = 1/(p:ℚ) := by simpa using hz
  have hh : (p:ℚ)*(z:ℚ) = 1 := by
    rw [hz']
    field_simp
  have hi : (p:ℤ)*z = 1 := by exact_mod_cast hh
  apply hp.not_dvd_one
  exact Int.natCast_dvd_natCast.mp ⟨z,hi.symm⟩

end LogicLineages.ModelsAlgebra.PGroups
