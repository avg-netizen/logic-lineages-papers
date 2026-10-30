module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicSocleCoordinates
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_cyclic_socle_coordinate_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicSocleCoordinateInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_socle_coordinate_injective

theorem fixed_cyclic_socle_coordinate_range : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicSocleCoordinateRange :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_socle_coordinate_range

theorem fixed_cyclic_socle_root_composition : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicSocleRootComposition :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_socle_root_composition

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
