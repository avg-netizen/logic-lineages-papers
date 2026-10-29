module

public import LogicLineages.OrdinalComparison.ActualTailSeparation
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLimitPartMonotone : Targets.ActualLimitPartMonotone :=
  actualLimitPartMonotone

theorem fixed_actualMaximumJointMonotone : Targets.ActualMaximumJointMonotone :=
  actualMaximumJointMonotone

theorem fixed_actualDescentJointMonotone : Targets.ActualDescentJointMonotone :=
  actualDescentJointMonotone

theorem fixed_actualReplacementCountJointMonotone : Targets.ActualReplacementCountJointMonotone :=
  actualReplacementCountJointMonotone

theorem fixed_controlIterateDoubleTowerGap : Targets.ControlIterateDoubleTowerGap :=
  controlIterateDoubleTowerGap

theorem fixed_actualTailSeparation : Targets.ActualTailSeparation :=
  actualTailSeparation

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
