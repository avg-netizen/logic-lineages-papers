module

public import LogicLineages.OrdinalComparison.WWTypedPartialProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualTypedHeadFreeCalibration : LogicLineages.OrdinalComparison.Source.Targets.ActualTypedHeadFreeCalibration :=
  LogicLineages.OrdinalComparison.Source.actualTypedHeadFreeCalibration

theorem fixed_actualTypedPartialSize : LogicLineages.OrdinalComparison.Source.Targets.ActualTypedPartialSize :=
  LogicLineages.OrdinalComparison.Source.actualTypedPartialSize

theorem fixed_actualTypedFreePartial : LogicLineages.OrdinalComparison.Source.Targets.ActualTypedFreePartial :=
  LogicLineages.OrdinalComparison.Source.actualTypedFreePartial

theorem fixed_actualTypedVariablePartial : LogicLineages.OrdinalComparison.Source.Targets.ActualTypedVariablePartial :=
  LogicLineages.OrdinalComparison.Source.actualTypedVariablePartial

theorem fixed_actualTypedSumPartial : LogicLineages.OrdinalComparison.Source.Targets.ActualTypedSumPartial :=
  LogicLineages.OrdinalComparison.Source.actualTypedSumPartial

theorem fixed_actualTypedExponentialPartial : LogicLineages.OrdinalComparison.Source.Targets.ActualTypedExponentialPartial :=
  LogicLineages.OrdinalComparison.Source.actualTypedExponentialPartial

theorem fixed_actualTypedCollapsePartial : LogicLineages.OrdinalComparison.Source.Targets.ActualTypedCollapsePartial :=
  LogicLineages.OrdinalComparison.Source.actualTypedCollapsePartial

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
