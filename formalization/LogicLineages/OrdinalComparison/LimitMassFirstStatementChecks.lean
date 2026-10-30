module

public import LogicLineages.OrdinalComparison.LimitMassFirstProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLimitMassFirstSuffixes : LogicLineages.OrdinalComparison.Targets.ActualLimitMassFirstSuffixes :=
  LogicLineages.OrdinalComparison.actualLimitMassFirstSuffixes

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
