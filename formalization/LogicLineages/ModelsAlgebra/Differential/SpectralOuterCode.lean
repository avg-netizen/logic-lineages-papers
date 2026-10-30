module

public import LogicLineages.ModelsAlgebra.Differential.SpectralResultantCodeTargets
public import LogicLineages.ModelsAlgebra.Differential.DensePolynomial

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode

open Polynomial

theorem outer_coefficients (p : OuterCode) (i : ℕ) :
    (outerValue p).coeff i = DensePolynomial.value (p.getD i []) := by
  induction p generalizing i with
  | nil => simp [outerValue, OrderOneAlgorithm.inputValue, DensePolynomial.value]
  | cons a as ih =>
    cases i with
    | zero => simp [outerValue, OrderOneAlgorithm.inputValue]
    | succ i => simpa only [outerValue, OrderOneAlgorithm.inputValue,
        coeff_add, coeff_C_succ, coeff_X_mul, zero_add, List.getD_cons_succ] using ih i

private theorem range_coefficients (m : ℕ) (f : ℕ → DensePolynomial.Code) (i : ℕ) :
    (outerValue ((List.range m).map f)).coeff i =
      if i < m then DensePolynomial.value (f i) else 0 := by
  rw [outer_coefficients]
  by_cases hi : i < m
  · rw [if_pos hi, List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map, List.getElem_range]
  · rw [if_neg hi, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    rfl

theorem outer_add_correct (a b : OuterCode) :
    outerValue (outerAdd a b) = outerValue a + outerValue b := by
  apply Polynomial.ext
  intro i
  rw [outerAdd, range_coefficients, coeff_add, outer_coefficients, outer_coefficients]
  by_cases hi : i < max a.length b.length
  · rw [if_pos hi, DensePolynomial.value_add]
  · rw [if_neg hi]
    have ha : a.length ≤ i := by omega
    have hb : b.length ≤ i := by omega
    rw [List.getD_eq_default _ _ ha, List.getD_eq_default _ _ hb]
    simp only [DensePolynomial.value, zero_add]

theorem outer_monomial_correct (a : DensePolynomial.Code) (k : ℕ) :
    outerValue (outerMonomial a k) = Polynomial.C (DensePolynomial.value a) * Polynomial.X ^ k := by
  induction k with
  | zero => simp [outerMonomial, outerValue, OrderOneAlgorithm.inputValue]
  | succ k ih =>
    have hs : outerMonomial a (k + 1) = [] :: outerMonomial a k := by
      simp [outerMonomial, List.replicate_succ]
    rw [hs]
    change C (DensePolynomial.value []) + X * outerValue (outerMonomial a k) = _
    rw [ih]
    simp only [DensePolynomial.value, map_zero, zero_add, pow_succ]
    ring

theorem outer_arithmetic : Targets.spectralOuterCodeArithmetic :=
  ⟨outer_add_correct, outer_monomial_correct⟩

end LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode
