module
public import LogicLineages.ModelsAlgebra.PGroups.CoprimeFiltrationTargets
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Data.Int.GCD
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem coprime_subgroup_membership : Targets.groupCoprimeSubgroupMembership.{u} := by
  intro G _ p hG S z hz x
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := hG x
    let q := QuotientAddGroup.mk' S
    have hqz : z • q x = 0 := by
      rw [← map_zsmul]
      exact (QuotientAddGroup.eq_zero_iff _).mpr hx
    have hqn : ((p ^ n : ℕ) : ℤ) • q x = 0 := by
      rw [natCast_zsmul, ← map_nsmul, hn, map_zero]
    have hg : Int.gcd z ((p ^ n : ℕ) : ℤ) = 1 := by
      simpa only [Int.gcd_def, Int.natAbs_natCast] using hz.pow_right n
    have he := (intGCD_nsmul_eq_zero).mpr ⟨hqz,hqn⟩
    rw [hg, one_nsmul] at he
    exact (QuotientAddGroup.eq_zero_iff _).mp he
  · intro hx
    exact S.zsmul_mem hx z

theorem coprime_filtration_membership : Targets.groupCoprimeFiltrationMembership.{u,v} := by
  intro G _ p hG z hz x α
  exact coprime_subgroup_membership G p hG (transfiniteFiltration p α) z hz x

end LogicLineages.ModelsAlgebra.PGroups
