module
public import LogicLineages.OrdinalComparison.BinaryPeriodSuppliersTargets
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

theorem actualFermatShapeTwoOrder : Targets.ActualFermatShapeTwoOrder := by
  intro r hr
  have hhalf : (2 : ZMod (2 ^ r + 1)) ^ r = -1 := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      ZMod.natCast_self (2 ^ r + 1)
  have hfull : (2 : ZMod (2 ^ r + 1)) ^ (2 * r) = 1 := by
    rw [Nat.mul_comm 2 r, pow_mul, hhalf]
    simp
  have hdiv := orderOf_dvd_of_pow_eq_one hfull
  have hpos : 0 < orderOf (2 : ZMod (2 ^ r + 1)) :=
    Nat.pos_of_dvd_of_pos hdiv (by omega)
  have hle : orderOf (2 : ZMod (2 ^ r + 1)) ≤ 2 * r := Nat.le_of_dvd (by omega) hdiv
  by_contra hne
  have hlt : orderOf (2 : ZMod (2 ^ r + 1)) < 2 * r := lt_of_le_of_ne hle hne
  obtain ⟨k, hk⟩ := hdiv
  have hk2 : 2 ≤ k := by nlinarith
  have hor : orderOf (2 : ZMod (2 ^ r + 1)) ≤ r := by nlinarith
  have hbound : 2 ^ orderOf (2 : ZMod (2 ^ r + 1)) < 2 ^ r + 1 :=
    Nat.lt_succ_of_le (Nat.pow_le_pow_right (by decide) hor)
  have hone : 1 < 2 ^ orderOf (2 : ZMod (2 ^ r + 1)) := one_lt_pow₀ (by decide) hpos.ne'
  have hq : 1 < 2 ^ r + 1 := by have hp := Nat.two_pow_pos r; omega
  have hcast : ((2 ^ orderOf (2 : ZMod (2 ^ r + 1)) : Nat) : ZMod (2 ^ r + 1)) =
      ((1 : Nat) : ZMod (2 ^ r + 1)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      pow_orderOf_eq_one (2 : ZMod (2 ^ r + 1))
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hbound, Nat.mod_eq_of_lt hq] at hv
  omega

private theorem source_exponent_sum (m : Nat) :
    (∑ i : Fin m, (i.val + 1)) = actualBinarySourceDimension m := by
  rw [← Finset.sum_range (fun n : Nat => n + 1)]
  change (∑ i ∈ Finset.range m, (i + 1)) = m * (m + 1) / 2
  calc
    (∑ i ∈ Finset.range m, (i + 1)) = ∑ i ∈ Finset.range (m + 1), i := by
      rw [Finset.sum_range_succ']; simp
    _ = m * (m + 1) / 2 := by rw [Finset.sum_range_id]; simp [Nat.mul_comm]

theorem actualBinarySourceReciprocity : Targets.ActualBinarySourceReciprocity.{u} := by
  intro K _ _ m z hz
  unfold actualBinarySourceDenominator
  simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
    Polynomial.eval₂_one, Polynomial.eval₂_X_pow]
  calc
    (∏ i : Fin m, (1 + z⁻¹ ^ (i.val + 1))) =
        ∏ i : Fin m, ((z ^ (i.val + 1))⁻¹ * (1 + z ^ (i.val + 1))) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [inv_pow, mul_add, mul_one, inv_mul_cancel₀ (pow_ne_zero _ hz), add_comm]
    _ = (∏ i : Fin m, z ^ (i.val + 1))⁻¹ * ∏ i : Fin m, (1 + z ^ (i.val + 1)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    _ = (z ^ actualBinarySourceDimension m)⁻¹ * ∏ i : Fin m, (1 + z ^ (i.val + 1)) := by
      rw [Finset.prod_pow_eq_pow_sum, source_exponent_sum]

end LogicLineages.OrdinalComparison
