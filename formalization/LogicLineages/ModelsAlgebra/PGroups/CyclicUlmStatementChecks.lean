module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicUlm
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_cyclic_top_ulm_isomorphism : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicTopUlmIsomorphism :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_top_ulm_isomorphism

theorem fixed_cyclic_ulm_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicUlmRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_ulm_rank

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
