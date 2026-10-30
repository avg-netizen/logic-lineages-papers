module

public import LogicLineages.ModelsAlgebra.PGroups.ReservoirStage
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_reservoir_stage_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReservoirStageIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reservoir_stage_isomorphism

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
