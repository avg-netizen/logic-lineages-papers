module

public import LogicLineages.OrdinalComparison.ActualLimitPredecessor
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actual_limit_saturation : Targets.ActualLimitMaximumPredecessorSaturation :=
  actualLimitMaximumPredecessorSaturation

theorem fixed_actual_limit_strict_growth : Targets.ActualLimitMaximumPredecessorStrictGrowth :=
  actualLimitMaximumPredecessorStrictGrowth

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
