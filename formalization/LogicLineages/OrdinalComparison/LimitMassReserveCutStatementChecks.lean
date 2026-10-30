module

public import LogicLineages.OrdinalComparison.LimitMassReserveCutProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLimitMassReserveCut : LogicLineages.OrdinalComparison.Targets.ActualLimitMassReserveCut :=
  LogicLineages.OrdinalComparison.actualLimitMassReserveCut

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
