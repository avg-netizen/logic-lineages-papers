module

public import LogicLineages.ModelsAlgebra.PGroups.BlockShift
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.BlockShiftStatementChecks

theorem fixed_finite_block_coordinates : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteBlockCoordinates :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_block_coordinates

theorem fixed_block_shift_coordinates : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBlockShiftCoordinates :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.block_shift_coordinates

theorem fixed_block_shift_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBlockShiftInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.block_shift_injective

theorem fixed_power_finsupp_socle_roots : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPowerFinsuppSocleRoots :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.power_finsupp_socle_roots

theorem fixed_block_shift_socle_roots : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBlockShiftSocleRoots :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.block_shift_socle_roots

theorem fixed_block_short_no_root : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBlockShortNoRoot :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.block_short_no_root

theorem fixed_block_shift_exponent : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBlockShiftExponent :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.block_shift_exponent

theorem fixed_block_shift_countable : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBlockShiftCountable :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.block_shift_countable

theorem fixed_block_shift_infinite : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBlockShiftInfinite :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.block_shift_infinite

end LogicLineages.ModelsAlgebra.PGroups.BlockShiftStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
