module

public import LogicLineages.ModelsAlgebra.PGroups.ReservoirRank
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_reservoir_whole_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReservoirWholeRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reservoir_whole_rank

theorem fixed_reservoir_stage_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReservoirStageRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reservoir_stage_rank

theorem fixed_reservoir_stage_nonisomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupReservoirStageNonisomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.reservoir_stage_nonisomorphism

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
