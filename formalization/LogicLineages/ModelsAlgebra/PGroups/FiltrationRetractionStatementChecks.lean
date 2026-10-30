module

public import LogicLineages.ModelsAlgebra.PGroups.FiltrationRetraction
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_hom_transfinite_filtration : LogicLineages.ModelsAlgebra.PGroups.Targets.groupHomTransfiniteFiltration :=
  LogicLineages.ModelsAlgebra.PGroups.hom_transfinite_filtration

theorem fixed_retraction_filtration_reflection : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRetractionFiltrationReflection :=
  LogicLineages.ModelsAlgebra.PGroups.retraction_filtration_reflection

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
