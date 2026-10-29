module
public import LogicLineages.OrdinalComparison.LimitPredecessor
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.CheckedLimitPredecessor

theorem exact_actual_ordinal_finite_tails : Targets.FiniteTailCorrect finiteTail :=
  finiteTailCorrect

theorem exact_source_limit_saturation :
    Targets.LimitMaximumPredecessorSaturation maximumPredecessor :=
  limitMaximumPredecessorSaturation

theorem exact_source_strict_budget_growth :
    Targets.LimitMaximumPredecessorStrictGrowth maximumPredecessor :=
  limitMaximumPredecessorStrictGrowth

end LogicLineages.OrdinalComparison.CheckedLimitPredecessor

#audit_namespace LogicLineages.OrdinalComparison
