module

public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicNormalForm
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_intrinsic_full_shift_normal_form : LogicLineages.ModelsAlgebra.PGroups.Targets.groupIntrinsicFullShiftNormalForm :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.intrinsic_full_shift_normal_form

theorem fixed_nonzero_lower_short_block : LogicLineages.ModelsAlgebra.PGroups.Targets.groupNonzeroLowerShortBlock :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.nonzero_lower_short_block

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
