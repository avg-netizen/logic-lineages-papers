module

public import LogicLineages.OrdinalComparison.CollectedWeightedPeakProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_collectedWeightedPeakBand : LogicLineages.OrdinalComparison.Targets.CollectedWeightedPeakBand :=
  LogicLineages.OrdinalComparison.collectedWeightedPeakBand

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
