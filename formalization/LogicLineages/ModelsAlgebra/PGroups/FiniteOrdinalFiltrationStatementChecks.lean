module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_finite_ordinal_filtration : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteOrdinalFiltration :=
  LogicLineages.ModelsAlgebra.PGroups.finite_ordinal_filtration

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
