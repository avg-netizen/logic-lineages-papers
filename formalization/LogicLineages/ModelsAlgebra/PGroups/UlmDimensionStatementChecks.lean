module

public import LogicLineages.ModelsAlgebra.PGroups.UlmDimension
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.UlmDimensionStatementChecks

theorem fixed_ulm_lower_rank_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUlmLowerRankFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.ulm_lower_rank_formula

theorem fixed_ulm_upper_rank_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUlmUpperRankFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.ulm_upper_rank_formula

theorem fixed_ulm_exact_rank_formula : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUlmExactRankFormula :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.ulm_exact_rank_formula

end LogicLineages.ModelsAlgebra.PGroups.UlmDimensionStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
