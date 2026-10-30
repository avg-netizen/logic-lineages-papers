module
public import LogicLineages.OrdinalComparison.PrimitiveRootDerivativeTargets
public import LogicLineages.OrdinalComparison.PrimitiveRootProductProof

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

private theorem source_polynomial_range (d : Nat) :
    actualBinarySourceDenominator d =
      ∏ i ∈ Finset.range d, (1 + Polynomial.X ^ (i + 1) : Polynomial (ZMod 2)) := by
  exact (Finset.prod_range (fun i : Nat => (1 + Polynomial.X ^ (i + 1) : Polynomial (ZMod 2)))).symm

private theorem source_eval_range {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (m : Nat) (z : K) :
    Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator m) =
      ∏ i ∈ Finset.range m, (1 + z ^ (i + 1)) := by
  rw [source_polynomial_range]
  simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
    Polynomial.eval₂_one, Polynomial.eval₂_X_pow]

theorem actualPrimitiveRootSourceDerivative : Targets.ActualPrimitiveRootSourceDerivative.{u} := by
  intro K _ _ q d hodd hqd hdq z hz
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hq : 1 ≤ q := by obtain ⟨k, hk⟩ := hodd; omega
  have hqs : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hqcast : (q : K) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.cast_add, Nat.cast_mul]
    simp [CharTwo.two_eq_zero]
  let T : Polynomial (ZMod 2) :=
    ∏ i ∈ Finset.range (d - q), (1 + Polynomial.X ^ (q + i + 1))
  have hprefix :
      (∏ i ∈ Finset.range q, (1 + Polynomial.X ^ (i + 1) : Polynomial (ZMod 2))) =
        actualBinarySourceDenominator (q - 1) * (1 + Polynomial.X ^ q) := by
    have h := Finset.prod_range_succ
      (fun i : Nat => (1 + Polynomial.X ^ (i + 1) : Polynomial (ZMod 2))) (q - 1)
    simpa only [hqs, ← source_polynomial_range] using h
  have hsplit : actualBinarySourceDenominator d =
      (actualBinarySourceDenominator (q - 1) * (1 + Polynomial.X ^ q)) * T := by
    rw [source_polynomial_range, show d = q + (d - q) by omega, Finset.prod_range_add, hprefix]
  have hT : Polynomial.eval₂ (algebraMap (ZMod 2) K) z T =
      Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator (d - q)) := by
    dsimp only [T]
    rw [source_eval_range]
    simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_add, Polynomial.eval₂_one,
      Polynomial.eval₂_X_pow]
    simp only [Nat.add_assoc, pow_add, hz.pow_eq_one, one_mul]
  have hzero : Polynomial.eval₂ (algebraMap (ZMod 2) K) z (1 + Polynomial.X ^ q) = 0 := by
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_X_pow,
      hz.pow_eq_one, CharTwo.add_self_eq_zero]
  have hinv : z ^ (q - 1) = z⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hqs, hz.pow_eq_one]
  have hderiv : Polynomial.eval₂ (algebraMap (ZMod 2) K) z
      (1 + Polynomial.X ^ q : Polynomial (ZMod 2)).derivative = z⁻¹ := by
    simp only [Polynomial.derivative_add, Polynomial.derivative_one, zero_add,
      Polynomial.derivative_X_pow, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow, map_natCast, Polynomial.eval₂_natCast, hqcast, one_mul, hinv]
  constructor
  · rw [hsplit]
    simp only [Polynomial.eval₂_mul, hzero, mul_zero, zero_mul]
  · rw [hsplit]
    simp only [Polynomial.derivative_mul, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      hzero, zero_mul, mul_zero, add_zero, zero_add,
      actualPrimitiveRootCompleteProduct K q hodd z hz, one_mul, hderiv, hT]

theorem actualPrimitiveRootSourceDerivativeNonzero :
    Targets.ActualPrimitiveRootSourceDerivativeNonzero.{u} := by
  intro K _ _ q d hodd hqd hdq z hz
  rw [(actualPrimitiveRootSourceDerivative K q d hodd hqd hdq z hz).2]
  have hq : q ≠ 0 := by obtain ⟨k, hk⟩ := hodd; omega
  exact mul_ne_zero (inv_ne_zero (hz.isUnit hq).ne_zero)
    (actualPrimitiveRootPartialProductNonzero K q (d - q) (by omega) z hz)

end LogicLineages.OrdinalComparison
