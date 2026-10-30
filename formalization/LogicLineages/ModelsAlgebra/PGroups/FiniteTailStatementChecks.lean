module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteTail
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_finite_tail_from_ranks : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteTailFromRanks :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_tail_from_ranks

theorem fixed_infinite_ulm_infinite_filtration : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInfiniteUlmInfiniteFiltration :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.infinite_ulm_infinite_filtration

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
