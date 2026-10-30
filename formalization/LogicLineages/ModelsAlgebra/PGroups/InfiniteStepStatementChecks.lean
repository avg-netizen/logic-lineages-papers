module

public import LogicLineages.ModelsAlgebra.PGroups.InfiniteStep
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_infinite_finite_step_ulm_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInfiniteFiniteStepUlmRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.infinite_finite_step_ulm_rank

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
