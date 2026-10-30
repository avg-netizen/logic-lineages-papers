module

public import LogicLineages.OrdinalComparison.ProfileReserveWordProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualProfileReserveWordConsumer : LogicLineages.OrdinalComparison.Targets.ActualProfileReserveWordConsumer :=
  LogicLineages.OrdinalComparison.actualProfileReserveWordConsumer

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
