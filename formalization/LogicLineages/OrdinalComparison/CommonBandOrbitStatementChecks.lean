module

public import LogicLineages.OrdinalComparison.CommonBandOrbitProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_commonBandOrbitCancellation : LogicLineages.OrdinalComparison.Targets.CommonBandOrbitCancellation :=
  LogicLineages.OrdinalComparison.commonBandOrbitCancellation

theorem fixed_actualCommonBandPeakInjectivity : LogicLineages.OrdinalComparison.Targets.ActualCommonBandPeakInjectivity :=
  LogicLineages.OrdinalComparison.actualCommonBandPeakInjectivity

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
