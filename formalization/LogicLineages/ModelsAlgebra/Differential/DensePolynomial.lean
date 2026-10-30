module

public import LogicLineages.ModelsAlgebra.Differential.DensePolynomialTargets
public import LogicLineages.ModelsAlgebra.Differential.RationalCode
public import Mathlib.Data.List.GetD

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.DensePolynomial

open Polynomial

theorem coefficients : Targets.densePolynomialCoefficients := by
  intro c
  induction c with
  | nil => intro i; simp [value, RationalCode.value_zero]
  | cons a as ih =>
    intro i
    cases i with
    | zero => simp [value, Polynomial.coeff_X_mul_zero]
    | succ i => simpa only [value, coeff_add, coeff_C_succ, coeff_X_mul,
        zero_add, List.getD_cons_succ] using ih i

theorem coefficient_outside (a : Code) (i : ℕ) (hi : a.length ≤ i) :
    (value a).coeff i = 0 := by
  rw [coefficients, List.getD_eq_default _ _ hi, RationalCode.value_zero]

private theorem coefficient_range (n : ℕ) (f : ℕ → RationalCode.Code) (i : ℕ) :
    (value ((List.range n).map f)).coeff i =
      if i < n then RationalCode.value (f i) else 0 := by
  rw [coefficients]
  by_cases hi : i < n
  · rw [if_pos hi, List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map, List.getElem_range]
  · rw [if_neg hi, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
      RationalCode.value_zero]

theorem value_add (a b : Code) : value (add a b) = value a + value b := by
  ext i
  rw [Polynomial.coeff_add, add, coefficient_range]
  by_cases hi : i < max a.length b.length
  · rw [if_pos hi, RationalCode.value_add, coefficients, coefficients]
  · rw [if_neg hi,
      coefficient_outside a i (le_trans (le_max_left _ _) (Nat.le_of_not_gt hi)),
      coefficient_outside b i (le_trans (le_max_right _ _) (Nat.le_of_not_gt hi))]
    simp

theorem value_neg (a : Code) : value (neg a) = -value a := by
  induction a with
  | nil => simp [neg, value]
  | cons c cs ih =>
    change C (RationalCode.value (RationalCode.neg c)) + X * value (neg cs) =
      -(C (RationalCode.value c) + X * value cs)
    rw [RationalCode.value_neg, ih, map_neg]
    ring

theorem value_scale (a : RationalCode.Code) (b : Code) :
    value (scale a b) = C (RationalCode.value a) * value b := by
  induction b with
  | nil => simp [scale, value]
  | cons c cs ih =>
    change C (RationalCode.value (RationalCode.mul a c)) + X * value (scale a cs) =
      C (RationalCode.value a) * (C (RationalCode.value c) + X * value cs)
    rw [RationalCode.value_mul, ih, map_mul]
    ring

theorem value_mul (a b : Code) : value (mul a b) = value a * value b := by
  induction a with
  | nil => simp [mul, value]
  | cons c cs ih =>
    rw [mul, value_add, value_scale]
    change C (RationalCode.value c) * value b +
      (C (RationalCode.value RationalCode.zero) + X * value (mul cs b)) =
      (C (RationalCode.value c) + X * value cs) * value b
    rw [RationalCode.value_zero, ih, map_zero]
    ring

theorem value_power (a : Code) (n : ℕ) : value (power a n) = (value a)^n := by
  induction n with
  | zero => simp [power, value, RationalCode.value_one]
  | succ n ih => rw [power, value_mul, ih, pow_succ]; ring

theorem value_derivative (a : Code) : value (derivative a) = (value a).derivative := by
  ext i
  rw [derivative, coefficient_range, coeff_derivative]
  by_cases hi : i < a.length - 1
  · rw [if_pos hi, RationalCode.value_mul, coefficients]
    simp only [RationalCode.value, Nat.cast_zero, sub_zero, zero_add, div_one]
    push_cast
    ring
  · rw [if_neg hi, coefficient_outside a (i + 1) (by omega), zero_mul]

theorem isZero_correct (a : Code) : isZero a = true ↔ value a = 0 := by
  induction a with
  | nil => simp [isZero, value]
  | cons c cs ih =>
    change (RationalCode.isZero c && isZero cs) = true ↔
      C (RationalCode.value c) + X * value cs = 0
    rw [Bool.and_eq_true, RationalCode.isZero_correct]
    constructor
    · rintro ⟨hc, hs⟩
      rw [hc, ih.mp hs]
      simp
    · intro h
      have hc : RationalCode.value c = 0 := by
        have hh := congrArg (fun p : Polynomial ℚ => p.coeff 0) h
        simpa using hh
      have hs : value cs = 0 := by
        ext i
        have hh := congrArg (fun p : Polynomial ℚ => p.coeff (i + 1)) h
        simpa only [coeff_add, coeff_C_succ, coeff_X_mul, coeff_zero, zero_add] using hh
      exact ⟨hc, ih.mpr hs⟩

theorem value_shift (n : ℕ) (a : Code) :
    value (List.replicate n RationalCode.zero ++ a) = X^n * value a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, value, RationalCode.value_zero,
      map_zero, zero_add, ih, pow_succ]
    ring

theorem coverage : Targets.densePolynomialCoverage := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨add a b, by rw [value_add, ha, hb]⟩
  | monomial n r =>
    obtain ⟨c, hc⟩ := RationalCode.coverage r
    refine ⟨List.replicate n RationalCode.zero ++ [c], ?_⟩
    rw [value_shift]
    simp only [value, hc, mul_zero, add_zero]
    rw [mul_comm, C_mul_X_pow_eq_monomial]

theorem arithmetic_correct : Targets.densePolynomialArithmeticCorrect :=
  ⟨value_add, value_neg, value_scale, value_mul, value_power, value_derivative, isZero_correct⟩

end LogicLineages.ModelsAlgebra.Differential.DensePolynomial
