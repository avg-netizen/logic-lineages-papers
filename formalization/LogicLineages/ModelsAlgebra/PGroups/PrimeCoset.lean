module
public import LogicLineages.ModelsAlgebra.PGroups.PrimeCosetTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

theorem prime_coset_order : Targets.groupPrimeCosetOrder.{u} := by
  intro G _ p _ B x hx hpx
  apply addOrderOf_eq_prime
  · rw [← map_nsmul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr hpx
  · intro h
    exact hx ((QuotientAddGroup.eq_zero_iff _).mp h)

theorem prime_coset_integer_membership : Targets.groupPrimeCosetIntegerMembership.{u} := by
  intro G _ p _ B x hx hpx z
  have ho := prime_coset_order G p B x hx hpx
  rw [← ho, addOrderOf_dvd_iff_zsmul_eq_zero, ← map_zsmul]
  exact (QuotientAddGroup.eq_zero_iff _).symm

end LogicLineages.ModelsAlgebra.PGroups
