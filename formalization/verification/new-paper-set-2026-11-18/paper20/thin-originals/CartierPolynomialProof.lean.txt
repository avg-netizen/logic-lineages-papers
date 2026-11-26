module
public import LogicLineages.OrdinalComparison.CartierPolynomialTargets
public import LogicLineages.OrdinalComparison.PolynomialDigitProof
public import Mathlib.Algebra.Polynomial.Expand

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualPolynomialSquareRootDigitCoefficient :
    Targets.ActualPolynomialSquareRootDigitCoefficient.{u} := by
  intro K _ _ _ b P n
  rw [actualPolynomialSquareRootDigit, Polynomial.coeff_map,
    actualBinaryPolynomialDigitCoefficient]
  exact (frobeniusEquiv K 2).apply_symm_apply _

private theorem square_coefficient {K : Type*} [Field K] [CharP K 2]
    (P : Polynomial K) (n : Nat) :
    (P ^ 2).coeff n = if 2 ∣ n then (P.coeff (n / 2)) ^ 2 else 0 := by
  rw [← Polynomial.map_frobenius_expand 2 P, Polynomial.coeff_map,
    Polynomial.coeff_expand (by decide)]
  split_ifs <;> simp [frobenius_def]

theorem actualPolynomialSquareRootDecomposition :
    Targets.ActualPolynomialSquareRootDecomposition.{u} := by
  intro K _ _ _ P
  ext n
  rw [Polynomial.coeff_add]
  cases n with
  | zero =>
    simp only [Polynomial.coeff_X_mul_zero, square_coefficient, dvd_zero, if_true,
      Nat.zero_div, add_zero]
    simpa [Nat.bit] using (actualPolynomialSquareRootDigitCoefficient K false P 0).symm
  | succ n =>
    rw [Polynomial.coeff_X_mul, square_coefficient, square_coefficient]
    by_cases h : 2 ∣ n + 1
    · have hn : ¬ 2 ∣ n := by omega
      rw [if_pos h, if_neg hn, add_zero, actualPolynomialSquareRootDigitCoefficient]
      congr 1
      change n + 1 = 2 * ((n + 1) / 2)
      omega
    · have hn : 2 ∣ n := by omega
      rw [if_neg h, if_pos hn, zero_add, actualPolynomialSquareRootDigitCoefficient]
      congr 1
      change n + 1 = 2 * (n / 2) + 1
      omega

end LogicLineages.OrdinalComparison
