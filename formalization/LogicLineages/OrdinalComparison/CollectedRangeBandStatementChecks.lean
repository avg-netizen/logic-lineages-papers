module

public import LogicLineages.OrdinalComparison.CollectedRangeBandProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualOmegaHeadFormula : LogicLineages.OrdinalComparison.Targets.ActualOmegaHeadFormula :=
  LogicLineages.OrdinalComparison.actualOmegaHeadFormula

theorem fixed_collectedRangeThresholdCode : LogicLineages.OrdinalComparison.Targets.CollectedRangeThresholdCode :=
  LogicLineages.OrdinalComparison.collectedRangeThresholdCode

theorem fixed_collectedNonlinearRangeBand : LogicLineages.OrdinalComparison.Targets.CollectedNonlinearRangeBand :=
  LogicLineages.OrdinalComparison.collectedNonlinearRangeBand

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
