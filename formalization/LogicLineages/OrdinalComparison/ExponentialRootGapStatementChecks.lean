module

public import LogicLineages.OrdinalComparison.ExponentialRootGapProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualCubicExponentialEnvelope : LogicLineages.OrdinalComparison.Targets.ActualCubicExponentialEnvelope :=
  LogicLineages.OrdinalComparison.actualCubicExponentialEnvelope

theorem fixed_actualDiscreteRootCountGap : LogicLineages.OrdinalComparison.Targets.ActualDiscreteRootCountGap :=
  LogicLineages.OrdinalComparison.actualDiscreteRootCountGap

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
