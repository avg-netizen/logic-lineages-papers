module

public import LogicLineages.ModelsAlgebra.Differential.SpectralOuterCode

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode

open Polynomial

private theorem matrix_entry (n B : ℕ) (fc : DensePolynomial.Code)
    (i j : Fin (n + (n - 1))) :
    NumericDeterminant.entry (n + (n - 1)) (matrix n B fc) i.val j.val =
      sylvesterEntry n B fc i.val j.val := by
  let d := n + (n - 1)
  have hd : 0 < d := by have hi := i.isLt; omega
  have hindex : i.val * d + j.val < d * d := by
    calc
      _ < i.val * d + d := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * d := by rw [Nat.add_mul, one_mul]
      _ ≤ d * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt i.isLt)
  have hdiv : (i.val * d + j.val) / d = i.val := by
    rw [Nat.add_comm (i.val * d) j.val, Nat.add_mul_div_right _ _ hd,
      Nat.div_eq_of_lt j.isLt, zero_add]
  have hmod : (i.val * d + j.val) % d = j.val := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  rw [NumericDeterminant.entry, matrix]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_range] using hindex)]
  simp only [List.getElem_map, List.getElem_range]
  rw [hdiv, hmod]

theorem sylvester_correct : Targets.spectralSylvesterCodeCorrect := by
  intro n B fc
  apply Matrix.ext
  intro i j
  change DensePolynomial.value
    (NumericDeterminant.entry (n + (n - 1)) (matrix n B fc) i.val j.val) = _
  rw [matrix_entry]
  induction j using Fin.addCases with
  | left j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Fin.val_castAdd]
    change DensePolynomial.value (sylvesterEntry n B fc i.val j.val) =
      if i.val ∈ Set.Icc j.val (j.val + (n - 1)) then
        (outerValue (generating n B fc)).coeff (i.val - j.val) else 0
    rw [sylvesterEntry, if_pos j.isLt]
    simp only [Set.mem_Icc]
    split_ifs with h
    · exact (outer_coefficients (generating n B fc) (i.val - j.val)).symm
    · rfl
  | right j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Fin.val_natAdd]
    change DensePolynomial.value (sylvesterEntry n B fc i.val (n + j.val)) =
      if i.val ∈ Set.Icc j.val (j.val + n) then
        ((DensePolynomial.value fc).map (Polynomial.C : ℚ →+* Polynomial ℚ)).coeff
          (i.val - j.val) else 0
    rw [sylvesterEntry, if_neg (by omega), Nat.add_sub_cancel_left]
    simp only [Set.mem_Icc]
    split_ifs with h
    · simp only [coeff_map, DensePolynomial.value,
        mul_zero, add_zero]
      rw [DensePolynomial.coefficients fc (i.val - j.val)]
    · rfl

end LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode
