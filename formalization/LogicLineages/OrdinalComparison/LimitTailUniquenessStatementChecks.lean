module

public import LogicLineages.OrdinalComparison.LimitTailUniquenessProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLimitTailUniqueness : LogicLineages.OrdinalComparison.Targets.ActualLimitTailUniqueness :=
  LogicLineages.OrdinalComparison.actualLimitTailUniqueness

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
