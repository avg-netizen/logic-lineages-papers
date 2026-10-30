module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltrationTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem finite_ordinal_filtration : Targets.groupFiniteOrdinalFiltration := by
  intro G _ p n
  induction n with
  | zero => exact transfiniteFiltration_zero p
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, transfiniteFiltration_add_one, ih]
      rfl

end LogicLineages.ModelsAlgebra.PGroups
