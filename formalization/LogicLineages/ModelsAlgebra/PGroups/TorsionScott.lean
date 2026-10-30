module

public import LogicLineages.ModelsAlgebra.PGroups.TorsionScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.LocallyFiniteScott
public import Mathlib.GroupTheory.FiniteAbelian.Basic

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

universe u v

theorem torsion_locally_finite : Targets.groupTorsionLocallyFinite.{u} := by
  intro G _ ht n a
  let S : AddSubgroup G := AddSubgroup.closure (Set.range a)
  letI : Fintype (Set.range a) := (Set.finite_range a).fintype
  letI : AddGroup.FG S := AddGroup.closure_finite_fg (Set.range a)
  have hS : AddMonoid.IsTorsion S := by
    intro x
    obtain ⟨k, hk, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (ht (x : G))
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k, hk, Subtype.ext hx⟩
  letI : Finite S := AddCommGroup.finite_of_fg_torsion S hS
  exact Set.toFinite (S : Set G)

theorem p_primary_torsion : Targets.groupPPrimaryTorsion.{u} := by
  intro p hp G _ hprimary x
  obtain ⟨k, hk⟩ := hprimary x
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨p ^ k, pow_pos hp.pos k, hk⟩

theorem p_primary_no_sigma_two_scott : Targets.groupPPrimaryNoSigmaTwoScott.{u,v} := by
  intro p hp G _ _ _ hprimary φ hφ
  exact locally_finite_no_sigma_two_scott G
    (torsion_locally_finite G (p_primary_torsion p hp G hprimary)) φ hφ

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
