module

public import LogicLineages.OrdinalComparison.CollectedFiniteTailProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_collectedFiniteTailSeparation : LogicLineages.OrdinalComparison.Targets.CollectedFiniteTailSeparation :=
  LogicLineages.OrdinalComparison.collectedFiniteTailSeparation

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
