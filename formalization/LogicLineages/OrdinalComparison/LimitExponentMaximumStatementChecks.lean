module

public import LogicLineages.OrdinalComparison.LimitExponentMaximumProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLimitExponentMaximum : LogicLineages.OrdinalComparison.Targets.ActualLimitExponentMaximum :=
  LogicLineages.OrdinalComparison.actualLimitExponentMaximum

theorem fixed_actualLimitExponentBudgetStrict : LogicLineages.OrdinalComparison.Targets.ActualLimitExponentBudgetStrict :=
  LogicLineages.OrdinalComparison.actualLimitExponentBudgetStrict

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
