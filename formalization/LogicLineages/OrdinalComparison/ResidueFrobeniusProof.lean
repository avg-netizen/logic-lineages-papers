module
public import LogicLineages.OrdinalComparison.ResidueFrobeniusTargets
public import LogicLineages.OrdinalComparison.LinkedResidueLaurentProof
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Tactic.LinearCombination

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

private theorem map_source_eval {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (f : K →+* K) (m : Nat) (z : K) :
    f (Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator m)) =
      Polynomial.eval₂ (algebraMap (ZMod 2) K) (f z) (actualBinarySourceDenominator m) := by
  simp [actualBinarySourceDenominator, Polynomial.eval₂_finsetProd, map_prod]

private theorem linked_root_half {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (u : Nat) (z : K) (hz : IsPrimitiveRoot z (actualLinkedModulus u)) :
    z ^ (2 ^ actualLinkedHalfExponent u) = z⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [← pow_succ, actualLinkedModulus] using hz.pow_eq_one

private theorem linked_root_full {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (u : Nat) (z : K) (hz : IsPrimitiveRoot z (actualLinkedModulus u)) :
    z ^ (2 ^ (2 * actualLinkedHalfExponent u)) = z := by
  rw [two_mul, pow_add, pow_mul, linked_root_half u z hz, inv_pow,
    linked_root_half u z hz, inv_inv]

theorem actualResidueFrobeniusUpperPeriod : Targets.ActualResidueFrobeniusUpperPeriod.{u} := by
  intro K _ _ u hu z hz
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hf := (actualLinkedResidueFormula K u hu z hz).1
  have h := congrArg (iterateFrobenius K 2 (2 * actualLinkedHalfExponent u)) hf
  rw [map_div₀, map_pow, map_source_eval] at h
  simp only [iterateFrobenius_def, linked_root_full u z hz] at h
  exact h.trans hf.symm

theorem actualResidueFrobeniusMidpointNonfixed :
    Targets.ActualResidueFrobeniusMidpointNonfixed.{u} := by
  intro K _ _ u hu z hz
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hz0 : z ≠ 0 := (hz.isUnit (show actualLinkedModulus u ≠ 0 from Nat.succ_ne_zero _)).ne_zero
  obtain ⟨hr, hD, heD, hpos, hupper, hqb, huB, hqd, hdq, hmq, hcomp⟩ :=
    actualLinkedResidueArithmetic u (by omega)
  let e := actualLinkedOffset u
  let D := actualLinkedDegree u
  let a := Polynomial.eval₂ (algebraMap (ZMod 2) K) z
    (actualBinarySourceDenominator (actualLinkedTail u))
  let b := (actualLinkedResidueExpansion u z).coeff (-1)
  have ha : a ≠ 0 := actualPrimitiveRootPartialProductNonzero K _ _ hmq z hz
  have hb : b = z ^ e / z ^ D * a := by
    have h := (actualLinkedResidueFormula K u hu z hz).2.1
    simpa only [zpow_sub₀ hz0, zpow_natCast, div_eq_mul_inv] using h
  have hmap := congrArg (iterateFrobenius K 2 (actualLinkedHalfExponent u)) hb
  rw [map_mul, map_div₀, map_pow, map_pow] at hmap
  change b ^ (2 ^ actualLinkedHalfExponent u) =
    (z ^ (2 ^ actualLinkedHalfExponent u)) ^ e /
    (z ^ (2 ^ actualLinkedHalfExponent u)) ^ D *
    (iterateFrobenius K 2 (actualLinkedHalfExponent u)) a at hmap
  rw [linked_root_half u z hz] at hmap
  have hma : (iterateFrobenius K 2 (actualLinkedHalfExponent u)) a =
      (z ^ D)⁻¹ * a := by
    dsimp [a]
    rw [map_source_eval, iterateFrobenius_def, linked_root_half u z hz,
      actualBinarySourceReciprocity K _ z hz0]
    rfl
  rw [hma] at hmap
  have hh : b ^ (2 ^ actualLinkedHalfExponent u) = a / z ^ e := by
    rw [hmap, inv_pow, inv_pow]
    field_simp
  intro hfixed
  have heq : z ^ D = z ^ (2 * e) := by
    have h := hh.symm.trans (hfixed.trans hb)
    have hze := pow_ne_zero e hz0
    have hzD := pow_ne_zero D hz0
    field_simp at h
    simpa only [← pow_mul, Nat.mul_comm] using h
  have hone : z ^ (D - 2 * e) = 1 := by
    rw [pow_sub₀ z hz0 (by dsimp [D, e]; omega), heq, mul_inv_cancel₀ (pow_ne_zero _ hz0)]
  exact (hz.pow_ne_one_of_pos_of_lt hpos.ne' hupper) hone

end LogicLineages.OrdinalComparison
