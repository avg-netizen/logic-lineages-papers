module

public import LogicLineages.ModelsAlgebra.PGroups.PrimeSquareTargets
public import Mathlib.Algebra.GroupWithZero.Divisibility

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem prime_square_inclusion_evaluation : Targets.groupPrimeSquareInclusionEvaluation := by
  intro p z
  exact ZMod.lift_coe p _ z

private theorem prime_square_cancel (p : ℕ) [Fact p.Prime] (z : ℤ)
    (h : p • (z : ZMod (p ^ 2)) = 0) : (p : ℤ) ∣ z := by
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hc : (((p : ℤ) * z : ℤ) : ZMod (p ^ 2)) = 0 := by
    simpa only [Int.cast_mul, Int.cast_natCast, nsmul_eq_mul] using h
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd ((p : ℤ) * z) (p ^ 2)).mp hc
  rw [Nat.cast_pow, pow_two] at hd
  exact (mul_dvd_mul_iff_left hp).mp hd

theorem prime_square_inclusion_injective : Targets.groupPrimeSquareInclusionInjective := by
  intro p _
  unfold primeSquareInclusion
  apply (ZMod.lift_injective p).mpr
  intro z hz
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mpr
  apply prime_square_cancel p z
  exact hz

theorem prime_square_inclusion_range : Targets.groupPrimeSquareInclusionRange := by
  intro p
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨t, rfl⟩ := ZMod.intCast_surjective u
    exact ⟨(t : ZMod (p ^ 2)), (prime_square_inclusion_evaluation p t).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨t, rfl⟩ := ZMod.intCast_surjective y
    exact ⟨(t : ZMod p), prime_square_inclusion_evaluation p t⟩

theorem prime_square_socle_roots : Targets.groupPrimeSquareSocleRoots := by
  intro p _ z hz
  obtain ⟨t, rfl⟩ := ZMod.intCast_surjective z
  obtain ⟨s, hs⟩ := prime_square_cancel p t hz
  refine ⟨(s : ZMod (p ^ 2)), ?_⟩
  rw [hs]
  simp only [Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
