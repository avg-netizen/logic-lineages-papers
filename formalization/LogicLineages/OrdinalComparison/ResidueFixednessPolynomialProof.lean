module
public import LogicLineages.OrdinalComparison.ResidueFixednessPolynomialTargets
public import LogicLineages.OrdinalComparison.LinkedResidueLaurentProof
public import LogicLineages.OrdinalComparison.BinaryDenominatorProof
public import Mathlib.Tactic.Positivity

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualResidueFixednessPolynomialSize : Targets.ActualResidueFixednessPolynomialSize := by
  intro u s hu hs
  have he : 0 < actualLinkedOffset u := by unfold actualLinkedOffset; omega
  have heD := (actualLinkedResidueArithmetic u (by omega)).2.2.1
  have heD' : actualLinkedOffset u < actualLinkedDegree u := by omega
  have hN : 1 < 2 ^ s := Nat.one_lt_pow (by omega) (by decide)
  have ht : 0 < (actualLinkedDegree u - actualLinkedOffset u) * (2 ^ s - 1) :=
    Nat.mul_pos (by omega) (by omega)
  refine ⟨he, heD', ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only [actualResidueFixednessPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, zero_pow ht.ne', zero_mul, add_zero]
    rw [← Polynomial.coeff_zero_eq_eval_zero, actualBinarySourceDenominatorConstant, one_pow]
  · have hlt : (actualLinkedDegree u - actualLinkedOffset u) * (2 ^ s - 1) +
        actualLinkedDegree u < 2 ^ s * actualLinkedDegree u := by
      have h1 := Nat.sub_add_cancel (Nat.le_of_lt heD')
      have h2 := Nat.sub_add_cancel (show 1 ≤ 2 ^ s by omega)
      nlinarith
    have hdeg : (actualBinarySourceDenominator (actualLinkedTail u)).degree =
        (actualLinkedDegree u : WithBot Nat) := actualBinarySourceDenominatorDegree _
    unfold actualResidueFixednessPolynomial
    rw [Polynomial.degree_add_eq_left_of_degree_lt]
    · simp only [Polynomial.degree_pow, hdeg, nsmul_eq_mul, Nat.cast_mul]
    · rw [Polynomial.degree_mul, Polynomial.degree_X_pow, Polynomial.degree_pow, hdeg]
      simpa only [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.cast_lt] using hlt

theorem actualResidueFixednessPolynomialRoot : Targets.ActualResidueFixednessPolynomialRoot.{u} := by
  intro K _ _ u s hu hs z hz hfixed
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hz0 : z ≠ 0 := (hz.isUnit (show actualLinkedModulus u ≠ 0 from Nat.succ_ne_zero _)).ne_zero
  have heD := (actualLinkedResidueArithmetic u (by omega)).2.2.1
  let t := actualLinkedDegree u - actualLinkedOffset u
  let a := Polynomial.eval₂ (algebraMap (ZMod 2) K) z
    (actualBinarySourceDenominator (actualLinkedTail u))
  let b := (actualLinkedResidueExpansion u z).coeff (-1)
  have hexp : (actualLinkedOffset u : Int) - (actualLinkedDegree u : Int) = -(t : Int) := by
    dsimp [t]; omega
  have hb : b = a / z ^ t := by
    have h := (actualLinkedResidueFormula K u hu z hz).2.1
    rw [hexp, zpow_neg, zpow_natCast] at h
    simpa only [div_eq_mul_inv, mul_comm] using h
  have ht0 : z ^ t ≠ 0 := pow_ne_zero _ hz0
  have hab : a = b * z ^ t := by rw [hb]; field_simp
  have hN : 2 ^ s - 1 + 1 = 2 ^ s := Nat.sub_add_cancel (show 1 ≤ 2 ^ s from one_le_pow₀ (by decide))
  have hp : a ^ (2 ^ s) = z ^ (t * (2 ^ s - 1)) * a := by
    calc
      a ^ (2 ^ s) = (b * z ^ t) ^ (2 ^ s) := congrArg (fun x : K => x ^ (2 ^ s)) hab
      _ = b * (z ^ t) ^ (2 ^ s) := by rw [mul_pow, hfixed]
      _ = (a / z ^ t) * ((z ^ t) ^ (2 ^ s - 1) * z ^ t) := by rw [hb, ← pow_succ, hN]
      _ = z ^ (t * (2 ^ s - 1)) * a := by rw [pow_mul]; field_simp
  simp only [actualResidueFixednessPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X]
  exact CharTwo.add_eq_zero.mpr hp

end LogicLineages.OrdinalComparison
