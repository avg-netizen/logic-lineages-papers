module

public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependenceTargets

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open scoped BigOperators
universe u

theorem finite_filtration_multiple_image : Targets.groupFiniteFiltrationMultipleImage.{u} := by
  intro G _ p j
  induction j with
  | zero =>
    ext x
    simp [finiteFiltration, multipleImage]
  | succ j ih =>
    rw [finiteFiltration, ih]
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      obtain ⟨z, hz⟩ := hy
      refine ⟨z, ?_⟩
      change p ^ (j + 1) • z = x
      change p ^ j • z = y at hz
      change p • y = x at hyx
      rw [pow_succ', mul_smul, hz]
      exact hyx
    · rintro ⟨z, hzx⟩
      refine ⟨p ^ j • z, ⟨z, rfl⟩, ?_⟩
      change p • (p ^ j • z) = x
      simpa only [nsmulAddMonoidHom_apply, pow_succ', mul_smul] using hzx

theorem ulm_finite_combination_kernel : Targets.groupUlmFiniteCombinationKernel.{u} := by
  intro p _ G _ S m x r
  let q : pSocle p S →+ UlmLayer p S := QuotientAddGroup.mk' (successorSocleSubgroup p S)
  let z : pSocle p S := ∑ i, (r i).val • x i
  have hq : q z = ∑ i, r i • q (x i) := by
    dsimp only [z]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  have hz : (z : G) = ∑ i, (r i).val • (x i : G) := by
    change (pSocle p S).subtype (∑ i, (r i).val • x i) = _
    rw [map_sum]
    simp only [map_nsmul]
    rfl
  change (∑ i, r i • q (x i)) = 0 ↔ _
  rw [← hq, ← hz]
  change (z : (pSocle p S) ⧸ successorSocleSubgroup p S) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  change ((z : G) ∈ pStep p S ∧ (nsmulAddMonoidHom p) (z : G) = 0) ↔ _
  exact and_iff_left z.property.2

theorem ulm_finite_independence : Targets.groupUlmFiniteIndependence.{u} := by
  classical
  intro p _ G _ j m x
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h r hr hmem
    have hzero := (ulm_finite_combination_kernel p G (finiteFiltration p j) m x r).mpr hmem
    exact hr (funext (h r hzero))
  · intro h r hzero
    have hr : r = 0 := by
      by_contra hne
      exact h r hne ((ulm_finite_combination_kernel p G (finiteFiltration p j) m x r).mp hzero)
    intro i
    simpa only [hr, Pi.zero_apply]

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
