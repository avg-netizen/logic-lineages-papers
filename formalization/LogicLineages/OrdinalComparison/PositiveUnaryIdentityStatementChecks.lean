module

public import LogicLineages.OrdinalComparison.PositiveUnaryIdentityProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualPositiveUnaryIdentity : LogicLineages.OrdinalComparison.Targets.ActualPositiveUnaryIdentity :=
  LogicLineages.OrdinalComparison.actualPositiveUnaryIdentity

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
