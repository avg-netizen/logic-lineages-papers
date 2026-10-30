module
public import LogicLineages.OrdinalComparison.PolynomialDigitTargets
public import Mathlib.Algebra.Polynomial.Coeff

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

theorem actualBinaryPolynomialDigitCoefficient : Targets.ActualBinaryPolynomialDigitCoefficient.{u} := by
  classical
  intro K _ b P n
  unfold actualBinaryPolynomialDigit
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single n]
  · exact Polynomial.coeff_monomial_same n _
  · intro i _ hin
    exact Polynomial.coeff_monomial_of_ne _ hin.symm
  · intro hn
    have hnlarge : P.natDegree < n := by
      have hnot : ¬n < P.natDegree + 1 := by intro hi; exact hn (Finset.mem_range.mpr hi)
      omega
    rw [Polynomial.coeff_monomial_same]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Nat.bit_val]; omega)

theorem actualBinaryPolynomialDigitSeries : Targets.ActualBinaryPolynomialDigitSeries.{u} := by
  intro K _ b P
  apply PowerSeries.ext
  intro n
  simpa only [Polynomial.coeff_coe, actualBinarySeriesDigit, PowerSeries.coeff_mk] using
    actualBinaryPolynomialDigitCoefficient K b P n

theorem actualBinaryPolynomialStepDegree : Targets.ActualBinaryPolynomialStepDegree.{u} := by
  intro K _ A U D hA hU b
  apply (Polynomial.degree_lt_iff_coeff_zero _ D).mpr
  intro n hn
  rw [actualBinaryPolynomialDigitCoefficient, Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  have hindex : i + j = Nat.bit b n := Finset.mem_antidiagonal.mp hij
  by_cases hi : i < D
  · have hj : D < j := by rw [Nat.bit_val] at hindex; omega
    have hzero := Polynomial.coeff_eq_zero_of_degree_lt
      (hA.trans_lt (WithBot.coe_lt_coe.mpr hj))
    rw [hzero, mul_zero]
  · have hzero := Polynomial.coeff_eq_zero_of_degree_lt
      (hU.trans_le (WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hi)))
    rw [hzero, zero_mul]

end LogicLineages.OrdinalComparison
