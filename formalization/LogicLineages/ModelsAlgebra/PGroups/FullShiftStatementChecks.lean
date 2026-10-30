module

public import LogicLineages.ModelsAlgebra.PGroups.FullShift
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.FullShiftStatementChecks

theorem fixed_full_shift_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFullShiftInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.full_shift_injective

theorem fixed_full_shift_socle_roots : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFullShiftSocleRoots :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.full_shift_socle_roots

theorem fixed_full_short_no_root : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFullShortNoRoot :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.full_short_no_root

theorem fixed_full_shift_exponent : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFullShiftExponent :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.full_shift_exponent

theorem fixed_full_shift_countable : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFullShiftCountable :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.full_shift_countable

theorem fixed_full_shift_infinite : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFullShiftInfinite :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.full_shift_infinite

end LogicLineages.ModelsAlgebra.PGroups.FullShiftStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
