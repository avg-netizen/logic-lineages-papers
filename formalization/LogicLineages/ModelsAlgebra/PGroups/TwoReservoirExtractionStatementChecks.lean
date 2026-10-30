module

public import LogicLineages.ModelsAlgebra.PGroups.TwoReservoirExtraction
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_two_reservoir_extraction : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTwoReservoirExtraction :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.two_reservoir_extraction

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
