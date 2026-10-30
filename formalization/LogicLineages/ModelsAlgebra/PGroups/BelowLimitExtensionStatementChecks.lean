module

public import LogicLineages.ModelsAlgebra.PGroups.BelowLimitExtension
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_below_limit_extension : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBelowLimitExtension :=
  LogicLineages.ModelsAlgebra.PGroups.below_limit_extension

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
