module

public import LogicLineages.ModelsAlgebra.PGroups.ReservoirChain
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_reservoir_monotone : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReservoirMonotone :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reservoir_monotone

theorem fixed_reservoir_cover : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReservoirCover :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reservoir_cover

theorem fixed_reservoir_map_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReservoirMapInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reservoir_map_injective

theorem fixed_reservoir_map_fixes : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReservoirMapFixes :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reservoir_map_fixes

theorem fixed_reservoir_tuple_fixing : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReservoirTupleFixing :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reservoir_tuple_fixing

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
