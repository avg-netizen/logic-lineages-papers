module

public import LogicLineages.ModelsAlgebra.PGroups.ShiftLimit
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.ShiftLimitStatementChecks

theorem fixed_shift_exponent : LogicLineages.ModelsAlgebra.PGroups.Targets.groupShiftExponent :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.shift_exponent

theorem fixed_shift_limit_socle_roots : LogicLineages.ModelsAlgebra.PGroups.Targets.groupShiftLimitSocleRoots :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.shift_limit_socle_roots

theorem fixed_shift_limit_not_isomorphic : LogicLineages.ModelsAlgebra.PGroups.Targets.groupShiftLimitNotIsomorphic :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.shift_limit_not_isomorphic

theorem fixed_shift_no_pi_two_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupShiftNoPiTwoScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.shift_no_pi_two_scott

end LogicLineages.ModelsAlgebra.PGroups.ShiftLimitStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
