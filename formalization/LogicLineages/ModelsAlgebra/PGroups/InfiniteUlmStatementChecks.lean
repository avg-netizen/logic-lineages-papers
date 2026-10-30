module

public import LogicLineages.ModelsAlgebra.PGroups.InfiniteUlm
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.InfiniteUlmStatementChecks

theorem fixed_infinite_ulm_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInfiniteUlmFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.infinite_ulm_formula

theorem fixed_countable_ulm_rank_bound : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCountableUlmRankBound :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.countable_ulm_rank_bound

theorem fixed_countable_infinite_ulm_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCountableInfiniteUlmFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.countable_infinite_ulm_formula

end LogicLineages.ModelsAlgebra.PGroups.InfiniteUlmStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
