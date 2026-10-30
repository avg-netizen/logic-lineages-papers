module

public import LogicLineages.ModelsAlgebra.PGroups.InternalProjection
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_internal_projection_existence : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInternalProjectionExistence :=
  LogicLineages.ModelsAlgebra.PGroups.internal_projection_existence

theorem fixed_internal_summand_filtration : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInternalSummandFiltration :=
  LogicLineages.ModelsAlgebra.PGroups.internal_summand_filtration

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
