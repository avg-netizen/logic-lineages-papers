module

public import LogicLineages.ModelsAlgebra.PGroups.SingleReservoirExtraction
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_single_reservoir_extraction : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSingleReservoirExtraction :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.single_reservoir_extraction

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
