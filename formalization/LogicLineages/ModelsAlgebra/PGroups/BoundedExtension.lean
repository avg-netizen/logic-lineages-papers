module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedExtensionTargets
public import LogicLineages.ModelsAlgebra.PGroups.CircleTorsion
public import Mathlib.Algebra.Category.Grp.Injective

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem bounded_cyclic_extension : Targets.groupBoundedCyclicExtension := by
  classical
  intro n _ G _ hbound S f
  let K : AddSubgroup UnitAddCircle := (nsmulAddMonoidHom n : UnitAddCircle →+ UnitAddCircle).ker
  obtain ⟨e⟩ := circle_torsion_isomorphism n
  let c : S →+ UnitAddCircle := K.subtype.comp (e.toAddMonoidHom.comp f)
  letI : Module.Injective ℤ UnitAddCircle := (Module.Baer.of_divisible UnitAddCircle).injective
  obtain ⟨h, hh⟩ := Module.Injective.out (R := ℤ) (Q := UnitAddCircle)
    S.subtype.toIntLinearMap Subtype.val_injective c.toIntLinearMap
  have hmem (x : G) : h x ∈ K := by
    change n • h x = 0
    rw [← map_nsmul, hbound, map_zero]
  let h' : G →+ K := h.toAddMonoidHom.codRestrict K hmem
  refine ⟨e.symm.toAddMonoidHom.comp h', ?_⟩
  intro x
  apply e.injective
  apply Subtype.ext
  change (e (e.symm (h' (x : G))) : UnitAddCircle) = (e (f x) : UnitAddCircle)
  rw [e.apply_symm_apply]
  exact hh x

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
