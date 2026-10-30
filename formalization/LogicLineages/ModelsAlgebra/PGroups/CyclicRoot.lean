module
public import LogicLineages.ModelsAlgebra.PGroups.CyclicRootTargets
public import Mathlib.Data.Nat.Prime.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem cyclic_root_evaluation : Targets.groupCyclicRootEvaluation := by
  intro n G _ y hy a
  exact ZMod.lift_coe n _ a

theorem cyclic_root_generator : Targets.groupCyclicRootGenerator := by
  intro n G _ y hy
  simpa only [Int.cast_one, one_zsmul] using cyclic_root_evaluation n G y hy (1 : ℤ)

theorem cyclic_root_order : Targets.groupCyclicRootOrder := by
  intro p _ G _ j y hy hz
  have hd : addOrderOf y ∣ p ^ (j+1) := (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hy
  obtain ⟨m,hm,he⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  have hn : ¬ m ≤ j := by
    intro h
    apply hz
    apply (addOrderOf_dvd_iff_nsmul_eq_zero).mp
    rw [he]
    exact pow_dvd_pow p h
  have hm' : m = j+1 := by omega
  simpa only [hm'] using he

theorem cyclic_root_injective : Targets.groupCyclicRootInjective := by
  intro p _ G _ j y hy hz
  unfold cyclicRootHom
  apply (ZMod.lift_injective (p ^ (j+1))).mpr
  intro a ha
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd a (p ^ (j+1))).mpr
  rw [← cyclic_root_order p G j y hy hz]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr ha

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
