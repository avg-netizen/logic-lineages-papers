module

public import LogicLineages.ModelsAlgebra.PGroups.EndomorphismLimit
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.EndomorphismLimitStatementChecks

theorem fixed_limit_stage_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupLimitStageInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.limit_stage_injective

theorem fixed_limit_stage_compatibility : LogicLineages.ModelsAlgebra.PGroups.Targets.groupLimitStageCompatibility :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.limit_stage_compatibility

theorem fixed_limit_ranges_monotone : LogicLineages.ModelsAlgebra.PGroups.Targets.groupLimitRangesMonotone :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.limit_ranges_monotone

theorem fixed_limit_range_cover : LogicLineages.ModelsAlgebra.PGroups.Targets.groupLimitRangeCover :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.limit_range_cover

theorem fixed_endomorphism_limit_countable : LogicLineages.ModelsAlgebra.PGroups.Targets.groupEndomorphismLimitCountable :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.endomorphism_limit_countable

end LogicLineages.ModelsAlgebra.PGroups.EndomorphismLimitStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
