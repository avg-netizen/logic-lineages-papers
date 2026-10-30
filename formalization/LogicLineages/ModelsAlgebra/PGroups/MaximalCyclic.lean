module

public import LogicLineages.ModelsAlgebra.PGroups.MaximalCyclicTargets
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Order.GroupWithZero.Basic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u

theorem maximal_cyclic_root_correction : Targets.groupMaximalCyclicRootCorrection.{u} := by
  intro p _ k G _ hbound y hy n x a ha
  by_cases hn : n ≤ k
  · have hz : (((p ^ (k - n) : ℕ) : ℤ) * a) • y = 0 := by
      rw [mul_smul, natCast_zsmul, ← ha, ← mul_smul, ← pow_add, Nat.sub_add_cancel hn]
      exact hbound x
    have hd : ((p ^ k : ℕ) : ℤ) ∣ ((p ^ (k - n) : ℕ) : ℤ) * a := by
      rw [← hy]
      exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hz
    have hpow : ((p ^ k : ℕ) : ℤ) =
        ((p ^ (k - n) : ℕ) : ℤ) * ((p ^ n : ℕ) : ℤ) := by
      rw [← Nat.cast_mul, ← pow_add, Nat.sub_add_cancel hn]
    rw [hpow] at hd
    have hp : ((p ^ (k - n) : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast pow_ne_zero (k - n) (Fact.out : p.Prime).ne_zero
    obtain ⟨b, hb⟩ := (mul_dvd_mul_iff_left hp).mp hd
    refine ⟨b, ?_⟩
    rw [ha, hb, mul_smul, natCast_zsmul]
  · have hx : p ^ n • x = 0 := by
      have he : p ^ n • x = p ^ (n - k) • (p ^ k • x) := by
        rw [← mul_smul, ← pow_add, Nat.sub_add_cancel (show k ≤ n by omega)]
      rw [he, hbound, smul_zero]
    exact ⟨0, by simp [hx]⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
