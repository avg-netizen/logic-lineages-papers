module

public import LogicLineages.OrdinalComparison.StrictMassLimitProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualIdentityProfileCalibration : LogicLineages.OrdinalComparison.Targets.ActualIdentityProfileCalibration :=
  LogicLineages.OrdinalComparison.actualIdentityProfileCalibration

theorem fixed_actualLimitKernelStrictMass : LogicLineages.OrdinalComparison.Targets.ActualLimitKernelStrictMass :=
  LogicLineages.OrdinalComparison.actualLimitKernelStrictMass

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
