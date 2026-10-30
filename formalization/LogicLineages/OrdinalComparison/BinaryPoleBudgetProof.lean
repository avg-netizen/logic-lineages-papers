module
public import LogicLineages.OrdinalComparison.BinaryPoleBudgetTargets
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Two

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualBinaryBinomialRootMultiplicity : Targets.ActualBinaryBinomialRootMultiplicity.{u} := by
  intro K _ _ n hn z
  let k := padicValNat 2 n
  let o := n / 2 ^ k
  have hpow : 2 ^ k ∣ n := pow_padicValNat_dvd
  have hfact : 2 ^ k * o = n := Nat.mul_div_cancel' hpow
  have hodd : ¬ 2 ∣ o := by
    intro ho
    apply (pow_succ_padicValNat_not_dvd (p := 2) hn.ne')
    change 2 ^ (k + 1) ∣ n
    rw [pow_succ]
    exact (Nat.mul_dvd_mul_left (2 ^ k) ho).trans (dvd_of_eq hfact)
  have hsep : (1 + Polynomial.X ^ o : Polynomial K).Separable := by
    simpa only [Polynomial.C_1, CharTwo.sub_eq_add, add_comm] using
      Polynomial.separable_X_pow_sub_C' 2 o (1 : K) hodd one_ne_zero
  have hexpand : Polynomial.expand K (2 ^ k) (1 + Polynomial.X ^ o) =
      (1 + Polynomial.X ^ n : Polynomial K) := by
    rw [map_add, map_one, map_pow, Polynomial.expand_X, ← pow_mul, hfact]
  rw [← hexpand, Polynomial.rootMultiplicity_expand_pow]
  have h := Polynomial.rootMultiplicity_le_one_of_separable hsep (z ^ (2 ^ k))
  simpa only [mul_one] using Nat.mul_le_mul_left (2 ^ k) h

private theorem rootMultiplicity_product {K : Type*} [Field K] {ι : Type*}
    (S : Finset ι) (P : ι → Polynomial K) (z : K) (hp : ∀ i ∈ S, P i ≠ 0) :
    (∏ i ∈ S, P i).rootMultiplicity z = ∑ i ∈ S, (P i).rootMultiplicity z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hi0 : P i ≠ 0 := hp i (by simp)
    have hs0 : ∀ j ∈ S, P j ≠ 0 := fun j hj => hp j (by simp [hj])
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Polynomial.rootMultiplicity_mul (mul_ne_zero hi0 (Finset.prod_ne_zero_iff.mpr hs0)), ih hs0]

theorem actualBinarySourceRootMultiplicity : Targets.ActualBinarySourceRootMultiplicity.{u} := by
  intro K _ _ d z
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hp : ∀ i : Fin d, (1 + Polynomial.X ^ (i.val + 1) : Polynomial K) ≠ 0 := by
    intro i h
    have hc := congrArg (fun P : Polynomial K => P.coeff 0) h
    simpa using hc
  have he : (actualBinarySourceDenominator d).map (algebraMap (ZMod 2) K) =
      ∏ i : Fin d, (1 + Polynomial.X ^ (i.val + 1) : Polynomial K) := by
    simp [actualBinarySourceDenominator, Polynomial.map_prod]
  rw [he, rootMultiplicity_product _ _ z (fun i _ => hp i)]
  exact Finset.sum_le_sum fun i _ => actualBinaryBinomialRootMultiplicity K (i.val + 1) (by omega) z

end LogicLineages.OrdinalComparison
