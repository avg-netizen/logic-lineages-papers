module

public import LogicLineages.PersistentMarking.ActualOmegaTowerTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.ActualOmegaTower
open scoped Ordinal

private theorem one_lt_omegaIndex : (1 : Ordinal.{0}) < omegaIndex :=
  Ordinal.one_lt_omega0.trans Ordinal.omega0_lt_omega_one

private theorem powerStep_normal : Ordinal.IsNormal powerStep :=
  Ordinal.isNormal_opow one_lt_omegaIndex

private theorem initial_lt : (0 : Ordinal.{0}) < powerStep 0 := by
  change (0 : Ordinal.{0}) < omegaIndex ^ (0 : Ordinal.{0})
  rw [Ordinal.opow_zero]
  exact zero_lt_one

theorem exact_LiteralRecurrence : LiteralRecurrence := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · change omegaIndex ^ (0 : Ordinal.{0}) = 1
    exact Ordinal.opow_zero omegaIndex
  · change omegaIndex ^ (omegaIndex ^ (0 : Ordinal.{0})) = omegaIndex
    rw [Ordinal.opow_zero, Ordinal.opow_one]
  · intro n
    change powerStep^[n + 1] 0 = powerStep (powerStep^[n] 0)
    exact Function.iterate_succ_apply' powerStep n 0

theorem exact_StrictlyIncreasing : StrictlyIncreasing := by
  apply strictMono_nat_of_lt_succ
  intro n
  change powerStep^[n] 0 < powerStep^[n + 1] 0
  rw [Function.iterate_succ_apply]
  exact powerStep_normal.strictMono.iterate n initial_lt

theorem exact_EndpointAsNfp : EndpointAsNfp := by
  change (⨆ n : Nat, powerStep^[n] 0) = Ordinal.nfp powerStep 0
  exact Ordinal.iSup_iterate_eq_nfp powerStep 0

theorem exact_BelowEndpoint : BelowEndpoint := by
  intro n
  rw [exact_EndpointAsNfp]
  exact Ordinal.iterate_lt_nfp powerStep_normal.strictMono initial_lt n

theorem exact_Cofinal : Cofinal := by
  intro a
  rw [exact_EndpointAsNfp]
  exact Ordinal.lt_nfp_iff

theorem exact_EndpointFixedPoint : EndpointFixedPoint := by
  change powerStep endpoint = endpoint
  rw [exact_EndpointAsNfp]
  exact Ordinal.nfp_fp powerStep_normal 0

theorem exact_EndpointLeast : EndpointLeast := by
  intro a ha
  rw [exact_EndpointAsNfp]
  exact Ordinal.nfp_le_fp powerStep_normal.monotone (zero_le : (0 : Ordinal.{0}) ≤ a) ha

theorem exact_FullActualOmegaTower : FullActualOmegaTower :=
  ⟨exact_LiteralRecurrence, exact_StrictlyIncreasing, exact_BelowEndpoint, exact_Cofinal,
    exact_EndpointAsNfp, exact_EndpointFixedPoint, exact_EndpointLeast⟩

#print axioms exact_LiteralRecurrence
#print axioms exact_StrictlyIncreasing
#print axioms exact_BelowEndpoint
#print axioms exact_Cofinal
#print axioms exact_EndpointAsNfp
#print axioms exact_EndpointFixedPoint
#print axioms exact_EndpointLeast
#print axioms exact_FullActualOmegaTower

end LogicLineages.PersistentMarking.ActualOmegaTower
