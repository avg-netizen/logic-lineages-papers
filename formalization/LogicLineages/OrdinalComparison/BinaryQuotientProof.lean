module
public import LogicLineages.OrdinalComparison.BinaryQuotientTargets
public import LogicLineages.OrdinalComparison.PolynomialDigitProof
public import LogicLineages.OrdinalComparison.SeriesObservabilityProof
public import Mathlib.Algebra.Polynomial.Expand

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem binary_expand_square (A : Polynomial (ZMod 2)) :
    Polynomial.expand (ZMod 2) 2 A = A ^ 2 := by
  have hf : frobenius (ZMod 2) 2 = RingHom.id (ZMod 2) := by
    ext a
    change a ^ 2 = a
    fin_cases a <;> decide
  simpa only [hf, Polynomial.map_id] using Polynomial.map_frobenius_expand 2 A

theorem actualBinaryPolynomialSquareCoefficient :
    Targets.ActualBinaryPolynomialSquareCoefficient := by
  intro A n
  rw [← binary_expand_square A]
  exact Polynomial.coeff_expand (by decide) A n

private theorem digit_add {K : Type*} [Field K] (b : Bool) (F G : PowerSeries K) :
    actualBinarySeriesDigit b (F + G) =
      actualBinarySeriesDigit b F + actualBinarySeriesDigit b G := by
  ext n
  simp [actualBinarySeriesDigit]

private theorem digit_mul_C {K : Type*} [Field K] (b : Bool) (F : PowerSeries K) (a : K) :
    actualBinarySeriesDigit b (F * PowerSeries.C a) =
      actualBinarySeriesDigit b F * PowerSeries.C a := by
  ext n
  simp [actualBinarySeriesDigit]

private theorem digit_mul_even_X {K : Type*} [Field K] (b : Bool)
    (F : PowerSeries K) (j : Nat) :
    actualBinarySeriesDigit b (F * PowerSeries.X ^ (j * 2)) =
      actualBinarySeriesDigit b F * PowerSeries.X ^ j := by
  apply PowerSeries.ext
  intro n
  simp only [actualBinarySeriesDigit, PowerSeries.coeff_mk, PowerSeries.coeff_mul_X_pow']
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  by_cases h : j ≤ n
  · have hbit : j * 2 ≤ Nat.bit b n := by rw [Nat.bit_val]; omega
    rw [if_pos hbit, if_pos h]
    have hindex : Nat.bit b n - j * 2 = Nat.bit b (n - j) := by
      simp only [Nat.bit_val]
      omega
    rw [hindex]
  · have hbit : ¬ j * 2 ≤ Nat.bit b n := by rw [Nat.bit_val]; omega
    rw [if_neg hbit, if_neg h]

private theorem digit_mul_expand {K : Type*} [Field K] (b : Bool)
    (F : PowerSeries K) (A : Polynomial K) :
    actualBinarySeriesDigit b (F * (Polynomial.expand K 2 A : PowerSeries K)) =
      actualBinarySeriesDigit b F * (A : PowerSeries K) := by
  induction A using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, Polynomial.coe_add, mul_add, digit_add, hP, hQ]
  | monomial j a =>
    rw [Polynomial.expand_monomial]
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
    rw [← mul_assoc, digit_mul_even_X, digit_mul_C, mul_assoc]

theorem actualBinarySeriesSquareFactor : Targets.ActualBinarySeriesSquareFactor := by
  intro b F A
  rw [← binary_expand_square A]
  exact digit_mul_expand b F A

theorem actualBinaryQuotientTransport : Targets.ActualBinaryQuotientTransport := by
  intro A U hA b
  have hc : PowerSeries.constantCoeff (A : PowerSeries (ZMod 2)) = 1 := by
    simpa only [Polynomial.constantCoeff_coe] using hA
  have hinv := PowerSeries.mul_inv_cancel (A : PowerSeries (ZMod 2))
    (by rw [hc]; exact one_ne_zero)
  have hproduct : actualPolynomialSeriesQuotient A U *
      ((A ^ 2 : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) =
        (U * A : Polynomial (ZMod 2)) := by
    rw [Polynomial.coe_pow, pow_two, ← mul_assoc, mul_comm (actualPolynomialSeriesQuotient A U),
      actualSeriesQuotientIdentity (ZMod 2) A U hA, Polynomial.coe_mul]
  have hstep : actualBinarySeriesDigit b (actualPolynomialSeriesQuotient A U) *
      (A : PowerSeries (ZMod 2)) = (actualBinaryPolynomialDigit b (U * A) : PowerSeries (ZMod 2)) := by
    rw [← actualBinarySeriesSquareFactor, hproduct,
      actualBinaryPolynomialDigitSeries (ZMod 2)]
  calc
    actualBinarySeriesDigit b (actualPolynomialSeriesQuotient A U) =
        (actualBinarySeriesDigit b (actualPolynomialSeriesQuotient A U) *
          (A : PowerSeries (ZMod 2))) * (A : PowerSeries (ZMod 2))⁻¹ := by
            rw [mul_assoc, hinv, mul_one]
    _ = actualPolynomialSeriesQuotient A (actualBinaryPolynomialDigit b (U * A)) := by
      rw [hstep]
      rfl

end LogicLineages.OrdinalComparison
