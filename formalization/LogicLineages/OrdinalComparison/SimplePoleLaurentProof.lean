module
public import LogicLineages.OrdinalComparison.SimplePoleLaurentTargets
public import Mathlib.Tactic.Ring

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

private theorem shifted_coefficient_zero {K : Type*} [Field K] (P : Polynomial K) (z : K) :
    (actualShiftedPolynomial P z).coeff 0 = P.eval z := by
  simp [actualShiftedPolynomial, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]

private theorem shifted_divX_coefficient_zero {K : Type*} [Field K] (P : Polynomial K) (z : K) :
    (actualShiftedPolynomial P z).divX.coeff 0 = P.derivative.eval z := by
  rw [Polynomial.coeff_divX]
  have hd : (actualShiftedPolynomial P z).derivative = actualShiftedPolynomial P.derivative z := by
    simp [actualShiftedPolynomial, Polynomial.derivative_comp]
  have h := congrArg (fun Q : Polynomial K => Q.coeff 0) hd
  simpa only [Polynomial.coeff_derivative, Nat.cast_zero, zero_add, Nat.cast_one, mul_one,
    shifted_coefficient_zero] using h

theorem actualSimplePoleExpansionReconstruction : Targets.ActualSimplePoleExpansionReconstruction.{u} := by
  intro K _ A U z hA hderiv
  let Q := (actualShiftedPolynomial A z).divX
  let N := (actualShiftedPolynomial U z : PowerSeries K)
  let E := HahnSeries.ofPowerSeries Int K
  have hden : actualShiftedPolynomial A z = Polynomial.X * Q := by
    have h := Polynomial.X_mul_divX_add (actualShiftedPolynomial A z)
    rw [shifted_coefficient_zero, hA, Polynomial.C_0, add_zero] at h
    exact h.symm
  have hc : PowerSeries.constantCoeff (Q : PowerSeries K) = A.derivative.eval z := by
    rw [Polynomial.constantCoeff_coe]
    exact shifted_divX_coefficient_zero A z
  have hinv : (Q : PowerSeries K) * (Q : PowerSeries K)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [hc]; exact hderiv)
  have hunit : E (Q : PowerSeries K) * E ((Q : PowerSeries K)⁻¹) = 1 := by
    rw [← map_mul, hinv, map_one]
  have hshift : (HahnSeries.single (1 : Int) (1 : K)) * HahnSeries.single (-1) 1 = 1 := by
    rw [HahnSeries.single_mul_single]
    norm_num
  unfold actualSimplePoleExpansion
  change E (actualShiftedPolynomial A z : PowerSeries K) *
    (HahnSeries.single (-1) 1 * E (N * (Q : PowerSeries K)⁻¹)) = E N
  rw [hden, Polynomial.coe_mul, Polynomial.coe_X, map_mul]
  have hEX : E PowerSeries.X = HahnSeries.single (1 : Int) (1 : K) := HahnSeries.ofPowerSeries_X
  rw [hEX]
  change (HahnSeries.single (1 : Int) (1 : K) * E (Q : PowerSeries K)) *
    (HahnSeries.single (-1) 1 * E (N * (Q : PowerSeries K)⁻¹)) = E N
  rw [map_mul]
  calc
    (HahnSeries.single 1 1 * E (Q : PowerSeries K)) *
        (HahnSeries.single (-1) 1 * (E N * E ((Q : PowerSeries K)⁻¹))) =
      (HahnSeries.single 1 1 * HahnSeries.single (-1) 1) *
        (E (Q : PowerSeries K) * E ((Q : PowerSeries K)⁻¹)) * E N := by ring
    _ = E N := by rw [hshift, hunit, one_mul, one_mul]

theorem actualSimplePoleExpansionResidue : Targets.ActualSimplePoleExpansionResidue.{u} := by
  intro K _ A U z _hA _hderiv
  unfold actualSimplePoleExpansion
  rw [HahnSeries.coeff_single_mul]
  simp only [sub_self, one_mul]
  have hzeroCoeff (F : PowerSeries K) :
      (HahnSeries.ofPowerSeries Int K F).coeff 0 = PowerSeries.coeff 0 F := by
    simpa only [Nat.cast_zero] using HahnSeries.ofPowerSeries_apply_coeff (Γ := Int) (R := K) F 0
  rw [hzeroCoeff, PowerSeries.coeff_zero_eq_constantCoeff,
    map_mul, PowerSeries.constantCoeff_inv, Polynomial.constantCoeff_coe,
    Polynomial.constantCoeff_coe, shifted_coefficient_zero, shifted_divX_coefficient_zero]
  rw [div_eq_mul_inv]

theorem actualSimplePoleExpansionLowerSupport : Targets.ActualSimplePoleExpansionLowerSupport.{u} := by
  intro K _ A U z _hA _hderiv n hn
  unfold actualSimplePoleExpansion
  rw [HahnSeries.coeff_single_mul, one_mul, HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨k, hk⟩
  change (k : Int) = n - (-1) at hk
  have hkpos : (0 : Int) ≤ (k : Int) := Int.natCast_nonneg k
  omega

end LogicLineages.OrdinalComparison
