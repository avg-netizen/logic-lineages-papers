module

public import LogicLineages.OrdinalComparison.ProfileDirectPackedProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualProfileDirectPackedState : LogicLineages.OrdinalComparison.Targets.ActualProfileDirectPackedState :=
  LogicLineages.OrdinalComparison.actualProfileDirectPackedState

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
