module

public import LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCodeTargets
public import LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomialBounds
public import LogicLineages.ModelsAlgebra.Differential.DensePolynomial

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCode

theorem digit_index : Targets.boxCodeDigitIndex := by
  intro n B C k
  change digitIndex B C k n = ∑ i : Fin n, ((k / B ^ i.val) % B) * C ^ i.val
  induction n with
  | zero => simp [digitIndex]
  | succ n ih =>
    simpa only [digitIndex, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last] using
      congrArg (fun z => z + ((k / B ^ n) % B) * C ^ n) ih

theorem monomial_calibration : Targets.boxCodeMonomial := by
  intro a k
  rw [monomial, DensePolynomial.value_scale, DensePolynomial.value_power]
  simp [DensePolynomial.value, RationalCode.value_zero, RationalCode.value_one]

private theorem rebaseAux_calibration (n B C : ℕ) (a : Code) (m : ℕ) :
    DensePolynomial.value (rebaseAux n B C a m) =
      ∑ k ∈ Finset.range m, Polynomial.C ((DensePolynomial.value a).coeff k) *
        Polynomial.X ^ digitIndex B C k n := by
  induction m with
  | zero => simp [rebaseAux, DensePolynomial.value]
  | succ m ih =>
    rw [rebaseAux, DensePolynomial.value_add, ih, monomial_calibration,
      Finset.sum_range_succ, DensePolynomial.coefficients]

theorem rebase_calibration : Targets.boxCodeRebase := by
  intro n B C a
  rw [rebase, rebaseAux_calibration, value, KroneckerPolynomial.decode, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [KroneckerPolynomial.monomial_encoding ℚ n C, digit_index]

theorem bound : Targets.boxCodeBound := by
  intro n B hB a
  exact KroneckerPolynomial.decoded_box ℚ n B hB (DensePolynomial.value a)

theorem coverage : Targets.boxCodeCoverage := by
  intro n p
  obtain ⟨B, hB, hp⟩ := KroneckerPolynomial.box_exists ℚ n p
  obtain ⟨a, ha⟩ := DensePolynomial.coverage (KroneckerPolynomial.encode B p)
  refine ⟨B, a, hB, ?_⟩
  rw [value, ha]
  exact KroneckerPolynomial.decode_encode ℚ n B hB p hp

end LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCode
