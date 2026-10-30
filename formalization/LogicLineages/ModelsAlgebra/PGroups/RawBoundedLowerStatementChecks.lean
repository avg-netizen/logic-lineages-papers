module

public import LogicLineages.ModelsAlgebra.PGroups.RawBoundedLower
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_raw_bounded_no_sigma_two_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawBoundedNoSigmaTwoScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_bounded_no_sigma_two_scott

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
