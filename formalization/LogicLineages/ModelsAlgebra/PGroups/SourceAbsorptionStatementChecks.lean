module

public import LogicLineages.ModelsAlgebra.PGroups.SourceAbsorption
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_absorption_tuple_transport : LogicLineages.ModelsAlgebra.PGroups.Targets.groupAbsorptionTupleTransport :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.absorption_tuple_transport

theorem fixed_source_factor_absorption : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSourceFactorAbsorption :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.source_factor_absorption

theorem fixed_source_bounded_absorption : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSourceBoundedAbsorption :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.source_bounded_absorption

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
