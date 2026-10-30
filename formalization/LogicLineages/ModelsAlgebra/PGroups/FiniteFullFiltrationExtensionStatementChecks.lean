module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteFullFiltrationExtension
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_finite_full_filtration_extension : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteFullFiltrationExtension :=
  LogicLineages.ModelsAlgebra.PGroups.finite_full_filtration_extension

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
