module
public import LogicLineages.OrdinalComparison.BinaryPartitionSeriesTargets
public import LogicLineages.OrdinalComparison.BinaryDenominatorProof
public import LogicLineages.OrdinalComparison.RestrictedPartitionPeriodProof
public import Mathlib.Algebra.CharP.Two

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualBinaryPartitionSeriesBase : Targets.ActualBinaryPartitionSeriesBase := by
  apply PowerSeries.ext
  intro n
  simp only [actualBinaryPartitionSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  by_cases hn : n = 0
  · subst n
    haveI : Nonempty (RestrictedPartitionState 0 0) :=
      ⟨⟨Fin.elim0, by simp [restrictedPartitionWeight]⟩⟩
    haveI : Subsingleton (RestrictedPartitionState 0 0) :=
      ⟨fun a b => Subtype.ext (funext fun i => Fin.elim0 i)⟩
    simp [restrictedPartitionCount]
  · haveI : IsEmpty (RestrictedPartitionState 0 n) := ⟨fun a => by
      apply hn
      simpa [restrictedPartitionWeight] using a.2.symm⟩
    simp [restrictedPartitionCount, hn]

theorem actualBinaryPartitionSeriesFactor : Targets.ActualBinaryPartitionSeriesFactor := by
  intro d
  apply PowerSeries.ext
  intro n
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_X_pow_mul']
  simp only [actualBinaryPartitionSeries, PowerSeries.coeff_mk]
  by_cases hn : d + 1 ≤ n
  · rw [if_pos hn]
    have hstep := restrictedPartitionStepRecurrence d (n - (d + 1))
    rw [Nat.sub_add_cancel hn] at hstep
    rw [hstep, Nat.cast_add, add_comm ((restrictedPartitionCount (d + 1) (n - (d + 1)) : Nat) : ZMod 2),
      CharTwo.add_cancel_right]
  · rw [if_neg hn, add_zero, restrictedPartitionLastCoordinateRecurrence]
    have hdiv : n / (d + 1) = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_ge hn)
    simp [hdiv]

theorem actualBinaryPartitionSeriesProduct : Targets.ActualBinaryPartitionSeriesProduct := by
  intro d
  induction d with
  | zero =>
    rw [actualBinaryPartitionSeriesBase]
    simp [actualBinarySourceDenominator]
  | succ d ih =>
    have hden : actualBinarySourceDenominator (d + 1) =
        actualBinarySourceDenominator d * (1 + Polynomial.X ^ (d + 1)) := by
      simp [actualBinarySourceDenominator, Fin.prod_univ_castSucc]
    rw [hden, Polynomial.coe_mul, mul_assoc]
    simp only [Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X]
    rw [actualBinaryPartitionSeriesFactor, ih]

theorem actualBinaryPartitionSeriesQuotient : Targets.ActualBinaryPartitionSeriesQuotient := by
  intro d
  have hc : PowerSeries.constantCoeff (actualBinarySourceDenominator d : PowerSeries (ZMod 2)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, actualBinarySourceDenominatorConstant]
    exact one_ne_zero
  have hinv := PowerSeries.inv_mul_cancel (actualBinarySourceDenominator d : PowerSeries (ZMod 2)) hc
  calc
    actualBinaryPartitionSeries d =
        ((actualBinarySourceDenominator d : PowerSeries (ZMod 2))⁻¹ *
          (actualBinarySourceDenominator d : PowerSeries (ZMod 2))) * actualBinaryPartitionSeries d := by
      rw [hinv, one_mul]
    _ = (actualBinarySourceDenominator d : PowerSeries (ZMod 2))⁻¹ := by
      rw [mul_assoc, actualBinaryPartitionSeriesProduct, mul_one]
    _ = actualPolynomialSeriesQuotient (actualBinarySourceDenominator d) 1 := by
      simp [actualPolynomialSeriesQuotient]

end LogicLineages.OrdinalComparison
