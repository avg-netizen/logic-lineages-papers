module
public import LogicLineages.OrdinalComparison.CartierSelectionTargets
public import LogicLineages.OrdinalComparison.PoleMultiplicityProof
public import LogicLineages.OrdinalComparison.BinaryPartitionSeriesProof
public import LogicLineages.OrdinalComparison.CartierSupportProof
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualBinaryRationalOriginSeries : Targets.ActualBinaryRationalOriginSeries := by
  intro d U
  let A := actualBinarySourceDenominator d
  have hc : A.eval 0 = 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, actualBinarySourceDenominatorConstant]
  have ha : A ≠ 0 := by intro h; simpa [h] using hc
  have hm : A.rootMultiplicity 0 = 0 := Polynomial.rootMultiplicity_eq_zero (by
    change A.eval 0 ≠ 0
    rw [hc]
    exact one_ne_zero)
  have h := actualMultiplicityPoleExpansionCorrect (ZMod 2) A U ha 0
  simpa [actualBinaryRationalDifferential, actualMultiplicityPoleExpansion,
    actualRootRemovedDenominator, hm, actualShiftedPolynomial,
    actualPolynomialSeriesQuotient, A] using h

theorem actualDifferentialSelectedCoefficient : Targets.ActualDifferentialSelectedCoefficient := by
  intro d e ℓ he heℓ
  have hid : iterateFrobeniusEquiv (ZMod 2) 2 ℓ = RingEquiv.refl (ZMod 2) := by
    ext x
    change x ^ (2 ^ ℓ) = x
    fin_cases x
    · change (0 : ZMod 2) ^ (2 ^ ℓ) = 0
      exact zero_pow (pow_ne_zero _ (by decide : (2 : Nat) ≠ 0))
    · change (1 : ZMod 2) ^ (2 ^ ℓ) = 1
      exact one_pow _
  have h := actualDifferentialCartierIteratedCoefficient (ZMod 2) 0
    (actualBinaryRationalDifferential d (Polynomial.X ^ (e - 1))) ℓ 0
  rw [hid] at h
  simp only [RingEquiv.symm_refl, RingEquiv.refl_apply, zero_add, mul_one] at h
  have hpos : 1 ≤ 2 ^ ℓ := one_le_pow₀ (by decide)
  have hi : (2 : Int) ^ ℓ - 1 = ((2 ^ ℓ - 1 : Nat) : Int) := by
    rw [Nat.cast_sub hpos, Nat.cast_pow]
    rfl
  rw [hi, actualBinaryRationalOriginSeries, HahnSeries.ofPowerSeries_apply_coeff] at h
  rw [h]
  change PowerSeries.coeff (2 ^ ℓ - 1)
    (((Polynomial.X ^ (e - 1) : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) *
      (actualBinarySourceDenominator d : PowerSeries (ZMod 2))⁻¹) = _
  have hp : actualBinaryPartitionSeries d =
      (actualBinarySourceDenominator d : PowerSeries (ZMod 2))⁻¹ := by
    simpa [actualPolynomialSeriesQuotient] using actualBinaryPartitionSeriesQuotient d
  rw [← hp, Polynomial.coe_pow, Polynomial.coe_X, PowerSeries.coeff_X_pow_mul',
    if_pos (by omega : e - 1 ≤ 2 ^ ℓ - 1)]
  have hn : 2 ^ ℓ - 1 - (e - 1) = 2 ^ ℓ - e := by omega
  rw [hn]
  simp [actualBinaryPartitionSeries]

theorem actualDifferentialSelectedParity : Targets.ActualDifferentialSelectedParity := by
  intro d e ℓ he heℓ
  rw [actualDifferentialSelectedCoefficient d e ℓ he heℓ]
  exact ZMod.val_natCast _ _

end LogicLineages.OrdinalComparison
