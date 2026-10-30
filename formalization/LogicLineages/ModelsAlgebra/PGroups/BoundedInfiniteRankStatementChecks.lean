module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedInfiniteRank
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_bounded_infinite_rank_exists : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedInfiniteRankExists :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_infinite_rank_exists

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
