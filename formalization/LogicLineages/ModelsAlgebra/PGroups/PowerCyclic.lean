module

public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclicTargets
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Order.GroupWithZero.Basic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem power_cyclic_inclusion_evaluation : Targets.groupPowerCyclicInclusionEvaluation := by
  intro p ℓ k h z
  exact ZMod.lift_coe (p ^ ℓ) _ z

private theorem power_cyclic_cancel (p : ℕ) [Fact p.Prime] (ℓ k : ℕ) (h : ℓ ≤ k)
    (z : ℤ) (hz : p ^ (k - ℓ) • (z : ZMod (p ^ k)) = 0) :
    ((p ^ ℓ : ℕ) : ℤ) ∣ z := by
  have hp : (((p ^ (k - ℓ) : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast pow_ne_zero (k - ℓ) (Fact.out : p.Prime).ne_zero
  have hc : ((((p ^ (k - ℓ) : ℕ) : ℤ) * z : ℤ) : ZMod (p ^ k)) = 0 := by
    simpa only [Int.cast_mul, Int.cast_natCast, nsmul_eq_mul] using hz
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ k)).mp hc
  have hpow : ((p ^ k : ℕ) : ℤ) =
      ((p ^ (k - ℓ) : ℕ) : ℤ) * ((p ^ ℓ : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, ← pow_add, Nat.sub_add_cancel h]
  rw [hpow] at hd
  exact (mul_dvd_mul_iff_left hp).mp hd

theorem power_cyclic_inclusion_injective : Targets.groupPowerCyclicInclusionInjective := by
  intro p _ ℓ k h
  unfold powerCyclicInclusion
  apply (ZMod.lift_injective (p ^ ℓ)).mpr
  intro z hz
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd z (p ^ ℓ)).mpr
  exact power_cyclic_cancel p ℓ k h z hz

theorem power_cyclic_inclusion_range : Targets.groupPowerCyclicInclusionRange := by
  intro p ℓ k h
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨t, rfl⟩ := ZMod.intCast_surjective u
    exact ⟨(t : ZMod (p ^ k)), (power_cyclic_inclusion_evaluation p ℓ k h t).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨t, rfl⟩ := ZMod.intCast_surjective y
    exact ⟨(t : ZMod (p ^ ℓ)), power_cyclic_inclusion_evaluation p ℓ k h t⟩

theorem power_cyclic_socle_roots : Targets.groupPowerCyclicSocleRoots := by
  intro p _ k hk z hz
  obtain ⟨t, rfl⟩ := ZMod.intCast_surjective z
  have hdiff : k - (k - 1) = 1 := by omega
  have hd := power_cyclic_cancel p (k - 1) k (Nat.sub_le _ _) t
    (by simpa only [hdiff, pow_one] using hz)
  obtain ⟨s, hs⟩ := hd
  refine ⟨(s : ZMod (p ^ k)), ?_⟩
  rw [hs]
  simp only [Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]

theorem power_cyclic_socle_witness : Targets.groupPowerCyclicSocleWitness := by
  intro p _ ℓ hℓ
  have hp := (Fact.out : p.Prime)
  constructor
  · have he : p * p ^ (ℓ - 1) = p ^ ℓ := by
      rw [← pow_succ']
      congr 1
      omega
    rw [nsmul_eq_mul, ← Nat.cast_mul, he]
    exact ZMod.natCast_self (p ^ ℓ)
  · intro hz
    have hd := (ZMod.natCast_eq_zero_iff (p ^ (ℓ - 1)) (p ^ ℓ)).mp hz
    have hle := Nat.le_of_dvd (pow_pos hp.pos (ℓ - 1)) hd
    exact (not_le_of_gt (pow_lt_pow_right₀ hp.one_lt (show ℓ - 1 < ℓ by omega))) hle

theorem power_cyclic_annihilation : Targets.groupPowerCyclicAnnihilation := by
  intro p ℓ n h x
  calc
    p ^ n • x = p ^ (n - ℓ) • (p ^ ℓ • x) := by
      rw [← mul_nsmul, ← pow_add, Nat.add_sub_of_le h]
    _ = 0 := by rw [ZModModule.char_nsmul_eq_zero (p ^ ℓ) x, nsmul_zero]

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
