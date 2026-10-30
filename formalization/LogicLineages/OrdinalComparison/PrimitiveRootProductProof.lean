module
public import LogicLineages.OrdinalComparison.PrimitiveRootProductTargets
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Two

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

theorem actualPrimitiveRootCompleteProduct : Targets.ActualPrimitiveRootCompleteProduct.{u} := by
  intro K _ _ q hodd z hz
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  obtain ⟨k, hk⟩ := hodd
  have hq : 1 ≤ q := by omega
  have hqcast : (q : K) = 1 := by
    rw [hk, Nat.cast_add, Nat.cast_mul]
    simp [CharTwo.two_eq_zero]
  have hz' : IsPrimitiveRoot z (q - 1 + 1) := by
    rw [Nat.sub_add_cancel hq]
    exact hz
  have hp := hz'.prod_one_sub_pow_eq_order
  have hcaststep : ((q - 1 : Nat) : K) + 1 = 1 := by
    calc
      _ = ((q - 1 + 1 : Nat) : K) := by rw [Nat.cast_add, Nat.cast_one]
      _ = (q : K) := by rw [Nat.sub_add_cancel hq]
      _ = 1 := hqcast
  have hp' : (∏ i ∈ Finset.range (q - 1), (1 + z ^ (i + 1))) = 1 := by
    simpa only [CharTwo.sub_eq_add, hcaststep] using hp
  unfold actualBinarySourceDenominator
  simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
    Polynomial.eval₂_one, Polynomial.eval₂_X_pow]
  rw [← Finset.prod_range (fun n : Nat => (1 + z ^ (n + 1)))]
  exact hp'

theorem actualPrimitiveRootPartialProductNonzero :
    Targets.ActualPrimitiveRootPartialProductNonzero.{u} := by
  intro K _ _ q m hmq z hz
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  unfold actualBinarySourceDenominator
  simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
    Polynomial.eval₂_one, Polynomial.eval₂_X_pow]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ hzero
  have hpow : z ^ (i.val + 1) ≠ 1 :=
    hz.pow_ne_one_of_pos_of_lt (Nat.succ_ne_zero _) (by omega)
  exact hpow (CharTwo.add_eq_zero.mp hzero).symm

end LogicLineages.OrdinalComparison
