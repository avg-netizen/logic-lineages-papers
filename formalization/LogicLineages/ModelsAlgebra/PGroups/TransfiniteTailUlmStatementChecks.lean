module

public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailUlm
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_transfinite_tail_ulm_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTransfiniteTailUlmIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.transfinite_tail_ulm_isomorphism

theorem fixed_transfinite_tail_ulm_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTransfiniteTailUlmRank :=
  LogicLineages.ModelsAlgebra.PGroups.transfinite_tail_ulm_rank

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
