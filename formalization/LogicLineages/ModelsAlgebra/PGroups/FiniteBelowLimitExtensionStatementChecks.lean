module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteBelowLimitExtension
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_finite_below_limit_extension : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteBelowLimitExtension :=
  LogicLineages.ModelsAlgebra.PGroups.finite_below_limit_extension

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
