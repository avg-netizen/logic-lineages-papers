module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedUlmTable
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.BoundedUlmTableStatementChecks

theorem fixed_positive_pi_all_complexity : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPositivePiAllComplexity :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.positive_pi_all_complexity

theorem fixed_ulm_rank_entry : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUlmRankEntry :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.ulm_rank_entry

theorem fixed_bounded_ulm_table : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedUlmTable :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_ulm_table

end LogicLineages.ModelsAlgebra.PGroups.BoundedUlmTableStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
