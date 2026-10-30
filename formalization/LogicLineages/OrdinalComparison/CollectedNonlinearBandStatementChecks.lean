module

public import LogicLineages.OrdinalComparison.CollectedNonlinearBandProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_collectedNonlinearInputBand : LogicLineages.OrdinalComparison.Targets.CollectedNonlinearInputBand :=
  LogicLineages.OrdinalComparison.collectedNonlinearInputBand

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
