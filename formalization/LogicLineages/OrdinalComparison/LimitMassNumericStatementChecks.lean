module

public import LogicLineages.OrdinalComparison.LimitMassNumericProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualPhiSquareGap : LogicLineages.OrdinalComparison.Targets.ActualPhiSquareGap :=
  LogicLineages.OrdinalComparison.actualPhiSquareGap

theorem fixed_actualLimitMassNumericalGap : LogicLineages.OrdinalComparison.Targets.ActualLimitMassNumericalGap :=
  LogicLineages.OrdinalComparison.actualLimitMassNumericalGap

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
