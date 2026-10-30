module

public import LogicLineages.ModelsAlgebra.PGroups.ZeroStageReduced
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_p_divisible_in_every_stage : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPDivisibleInEveryStage :=
  LogicLineages.ModelsAlgebra.PGroups.p_divisible_in_every_stage

theorem fixed_zero_stage_no_p_divisible : LogicLineages.ModelsAlgebra.PGroups.Targets.groupZeroStageNoPDivisible :=
  LogicLineages.ModelsAlgebra.PGroups.zero_stage_no_p_divisible

theorem fixed_zero_stage_reduced : LogicLineages.ModelsAlgebra.PGroups.Targets.groupZeroStageReduced :=
  LogicLineages.ModelsAlgebra.PGroups.zero_stage_reduced

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
