module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedCategoricity
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_bounded_ulm_categoricity : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedUlmCategoricity :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_ulm_categoricity

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
