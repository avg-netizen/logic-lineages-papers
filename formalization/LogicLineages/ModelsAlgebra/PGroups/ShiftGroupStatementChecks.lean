module

public import LogicLineages.ModelsAlgebra.PGroups.ShiftGroup
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.ShiftGroupStatementChecks

theorem fixed_shift_coordinates : LogicLineages.ModelsAlgebra.PGroups.Targets.groupShiftCoordinates :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.shift_coordinates

theorem fixed_shift_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupShiftInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.shift_injective

theorem fixed_square_finsupp_socle_roots : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSquareFinsuppSocleRoots :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.square_finsupp_socle_roots

theorem fixed_shift_socle_roots : LogicLineages.ModelsAlgebra.PGroups.Targets.groupShiftSocleRoots :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.shift_socle_roots

theorem fixed_shift_short_no_root : LogicLineages.ModelsAlgebra.PGroups.Targets.groupShiftShortNoRoot :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.shift_short_no_root

theorem fixed_shift_countable : LogicLineages.ModelsAlgebra.PGroups.Targets.groupShiftCountable :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.shift_countable

theorem fixed_shift_infinite : LogicLineages.ModelsAlgebra.PGroups.Targets.groupShiftInfinite :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.shift_infinite

end LogicLineages.ModelsAlgebra.PGroups.ShiftGroupStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
