module
public import LogicLineages.OrdinalComparison.BinaryMatrixTargets
public import LogicLineages.OrdinalComparison.BinaryPolynomialWordProof

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

private theorem proper_polynomial_sum {K : Type*} [Field K] (D : Nat) (U : Polynomial K)
    (hU : U.degree < (D : WithBot Nat)) :
    U = ∑ j : Fin D, Polynomial.monomial j.val (U.coeff j.val) := by
  classical
  apply Polynomial.ext
  intro n
  rw [Polynomial.finsetSum_coeff]
  by_cases hn : n < D
  · rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin D)]
    · simp
    · intro j _ hj
      have hne : j.val ≠ n := by intro he; apply hj; exact Fin.ext he
      simp [Polynomial.coeff_monomial, hne, hne.symm]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · rw [Polynomial.coeff_eq_zero_of_degree_lt
      (hU.trans_le (WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hn)))]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hne : n ≠ j.val := by intro he; subst n; exact hn j.isLt
    simp [Polynomial.coeff_monomial, hne, hne.symm]

theorem actualBinaryMatrixStep : Targets.ActualBinaryMatrixStep.{u} := by
  classical
  intro K _ D A U hU b
  funext i
  change (actualBinaryPolynomialDigit b (U * A)).coeff i.val = _
  rw [actualBinaryPolynomialDigitCoefficient]
  conv_lhs => rw [proper_polynomial_sum D U hU]
  rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
  change (∑ j : Fin D, (Polynomial.monomial j.val (U.coeff j.val) * A).coeff (Nat.bit b i.val)) =
    ∑ j : Fin D, (if j.val ≤ Nat.bit b i.val then A.coeff (Nat.bit b i.val - j.val) else 0) * U.coeff j.val
  apply Finset.sum_congr rfl
  intro j _
  rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  split_ifs <;> simp [mul_comm]

theorem actualBinaryMatrixWordCalibration : Targets.ActualBinaryMatrixWordCalibration.{u} := by
  intro K _ D A U hA hU w
  induction w generalizing U with
  | nil => rfl
  | cons b w ih =>
    simp only [actualBinaryMatrixWord, actualBinaryPolynomialWord]
    rw [← actualBinaryMatrixStep K D A U hU b]
    exact ih _ (actualBinaryPolynomialStepDegree K A U D hA hU b)

theorem actualBinaryMatrixWordObservation : Targets.ActualBinaryMatrixWordObservation := by
  intro D hD A U hA hdegree hU w
  rw [actualBinaryMatrixWordCalibration (ZMod 2) D A U hdegree hU w]
  exact actualBinaryPolynomialWordObservation A U hA w

theorem actualBinaryMatrixBoundedContinuation : Targets.ActualBinaryMatrixBoundedContinuation := by
  intro D hD A U V hA hdegree hU hV hne
  obtain ⟨w, hlen, hdiff⟩ := actualBinaryPolynomialBoundedContinuation A U V hA D hdegree hU hV hne
  refine ⟨w, hlen, ?_⟩
  rw [actualBinaryMatrixWordCalibration (ZMod 2) D A U hdegree hU w,
    actualBinaryMatrixWordCalibration (ZMod 2) D A V hdegree hV w]
  exact hdiff

end LogicLineages.OrdinalComparison
