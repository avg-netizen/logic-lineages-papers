module

public import LogicLineages.ModelsAlgebra.PGroups.AbsorptionMap
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_absorption_map_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupAbsorptionMapInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.absorption_map_injective

theorem fixed_absorption_map_fixes : LogicLineages.ModelsAlgebra.PGroups.Targets.groupAbsorptionMapFixes :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.absorption_map_fixes

theorem fixed_bounded_absorption_tuple_fixing : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedAbsorptionTupleFixing :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_absorption_tuple_fixing

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
