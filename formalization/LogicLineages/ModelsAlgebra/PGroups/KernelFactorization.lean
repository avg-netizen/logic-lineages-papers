module
public import LogicLineages.ModelsAlgebra.PGroups.KernelFactorizationTargets
public import Mathlib.GroupTheory.QuotientGroup.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

theorem kernel_factorization : Targets.groupKernelFactorization.{u} := by
  intro D S H _ _ _ f g hf hker
  let e := QuotientAddGroup.quotientKerEquivOfSurjective f hf
  let l := QuotientAddGroup.lift f.ker g hker.le
  have hl : Function.Injective l :=
    (QuotientAddGroup.injective_lift_iff f.ker g hker.le).mpr hker
  refine ⟨l.comp e.symm.toAddMonoidHom, hl.comp e.symm.injective, ?_⟩
  intro d
  have he : e ((QuotientAddGroup.mk' f.ker) d) = f d := rfl
  change l (e.symm (f d)) = g d
  rw [← he, e.symm_apply_apply]
  rfl

end LogicLineages.ModelsAlgebra.PGroups
