module

public import LogicLineages.OrdinalComparison.LimitMassPackedProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLimitMassPackedState : LogicLineages.OrdinalComparison.Targets.ActualLimitMassPackedState :=
  LogicLineages.OrdinalComparison.actualLimitMassPackedState

theorem fixed_actualLimitMassSecondMaximum : LogicLineages.OrdinalComparison.Targets.ActualLimitMassSecondMaximum :=
  LogicLineages.OrdinalComparison.actualLimitMassSecondMaximum

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
