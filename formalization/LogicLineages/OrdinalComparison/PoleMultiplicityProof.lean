module
public import LogicLineages.OrdinalComparison.PoleMultiplicityTargets
public import LogicLineages.OrdinalComparison.TranslatedRationalProof
public import Mathlib.Tactic.Ring

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualMultiplicityPoleExpansionCorrect : Targets.ActualMultiplicityPoleExpansion.{u} := by
  intro K _ A U hA z
  let m := A.rootMultiplicity z
  let B := actualRootRemovedDenominator A z
  let E := HahnSeries.ofPowerSeries Int K
  let Q : PowerSeries K := actualShiftedPolynomial B z
  have hB : B.eval z ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero z hA
  have hc : PowerSeries.constantCoeff Q = B.eval z := by
    simp [Q, Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
      actualShiftedPolynomial, Polynomial.eval_comp]
  have hunit : E Q * E (Q⁻¹) = 1 := by
    rw [← map_mul, PowerSeries.mul_inv_cancel _ (by rw [hc]; exact hB), map_one]
  have hinv : (E Q)⁻¹ = E (Q⁻¹) := inv_eq_of_mul_eq_one_right hunit
  have hx : actualTranslatedPolynomialEmbedding z (Polynomial.X - Polynomial.C z) =
      HahnSeries.single (1 : Int) (1 : K) := by
    rw [map_sub, actualTranslatedPolynomialVariable, actualTranslatedPolynomialConstant,
      add_sub_cancel_right]
  have hfac : actualTranslatedPolynomialEmbedding z A =
      HahnSeries.single (m : Int) 1 * actualTranslatedPolynomialEmbedding z B := by
    have h := congrArg (actualTranslatedPolynomialEmbedding z)
      (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq A z)
    simpa only [map_mul, map_pow, hx, HahnSeries.single_pow, nsmul_eq_mul,
      mul_one, one_pow, m, B, actualRootRemovedDenominator] using h.symm
  rw [map_div₀, actualTranslatedRationalPolynomial, actualTranslatedRationalPolynomial, hfac]
  rw [actualTranslatedPolynomialSeries K z B, actualTranslatedPolynomialSeries K z U]
  change E (actualShiftedPolynomial U z : PowerSeries K) /
    (HahnSeries.single (m : Int) 1 * E Q) = _
  rw [div_eq_mul_inv, mul_inv_rev, HahnSeries.inv_single, inv_one, hinv]
  change E (actualShiftedPolynomial U z : PowerSeries K) *
    (E (Q⁻¹) * HahnSeries.single (-(m : Int)) 1) =
      HahnSeries.single (-(m : Int)) 1 * E ((actualShiftedPolynomial U z : PowerSeries K) * Q⁻¹)
  rw [map_mul]
  ring

theorem actualMultiplicityPoleLowerSupport : Targets.ActualMultiplicityPoleLowerSupport.{u} := by
  intro K _ A U hA z n hn
  rw [actualMultiplicityPoleExpansionCorrect K A U hA z]
  unfold actualMultiplicityPoleExpansion
  rw [HahnSeries.coeff_single_mul, one_mul, HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨k, hk⟩
  change (k : Int) = n - (-(A.rootMultiplicity z : Int)) at hk
  have hkpos := Int.natCast_nonneg k
  omega

end LogicLineages.OrdinalComparison
