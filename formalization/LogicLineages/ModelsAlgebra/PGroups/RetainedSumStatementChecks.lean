module

public import LogicLineages.ModelsAlgebra.PGroups.RetainedSum
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_retained_sum_disjoint : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRetainedSumDisjoint :=
  LogicLineages.ModelsAlgebra.PGroups.retained_sum_disjoint

theorem fixed_retained_sum_quotient_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRetainedSumQuotientInjective :=
  LogicLineages.ModelsAlgebra.PGroups.retained_sum_quotient_injective

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
