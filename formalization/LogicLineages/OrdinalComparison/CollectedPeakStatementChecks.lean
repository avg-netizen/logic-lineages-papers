module

public import LogicLineages.OrdinalComparison.CollectedPeakProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_collectedPositiveInputLower : LogicLineages.OrdinalComparison.Targets.CollectedPositiveInputLower :=
  LogicLineages.OrdinalComparison.collectedPositiveInputLower

theorem fixed_collectedAtomNormDecomposition : LogicLineages.OrdinalComparison.Targets.CollectedAtomNormDecomposition :=
  LogicLineages.OrdinalComparison.collectedAtomNormDecomposition

theorem fixed_collectedHeadPeakBand : LogicLineages.OrdinalComparison.Targets.CollectedHeadPeakBand :=
  LogicLineages.OrdinalComparison.collectedHeadPeakBand

theorem fixed_collectedMaximumPeak : LogicLineages.OrdinalComparison.Targets.CollectedMaximumPeak :=
  LogicLineages.OrdinalComparison.collectedMaximumPeak

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
