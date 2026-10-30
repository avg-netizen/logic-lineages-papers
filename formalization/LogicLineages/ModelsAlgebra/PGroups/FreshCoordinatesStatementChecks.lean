module

public import LogicLineages.ModelsAlgebra.PGroups.FreshCoordinates
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_reserve_even_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReserveEvenInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reserve_even_injective

theorem fixed_reserve_odd_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReserveOddInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reserve_odd_injective

theorem fixed_reserve_ranges_disjoint : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReserveRangesDisjoint :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reserve_ranges_disjoint

theorem fixed_reserve_even_fixes : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReserveEvenFixes :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reserve_even_fixes

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
