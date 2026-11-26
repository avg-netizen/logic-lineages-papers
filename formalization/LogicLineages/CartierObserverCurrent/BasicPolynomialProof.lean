module
public import LogicLineages.CartierObserverCurrent.BasicTargets
public import Mathlib.Algebra.Polynomial.Expand
public import Lean.Elab.Tactic.Omega
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Basic

theorem actualBinaryPolynomialDigitCoefficient : ∀ (K : Type u) [Field K], ∀ b : Bool, ∀ P : Polynomial K, ∀ n : Nat,
    (actualBinaryPolynomialDigit b P).coeff n = P.coeff (Nat.bit b n) := by
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

#audit_namespace LogicLineages.CartierObserverCurrent.Basic
end LogicLineages.CartierObserverCurrent.Basic
