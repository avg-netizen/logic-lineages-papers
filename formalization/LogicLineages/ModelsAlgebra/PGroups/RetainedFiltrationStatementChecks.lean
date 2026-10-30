module

public import LogicLineages.ModelsAlgebra.PGroups.RetainedFiltration
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_retained_filtration_reflection : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRetainedFiltrationReflection :=
  LogicLineages.ModelsAlgebra.PGroups.retained_filtration_reflection

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
