module

public import LogicLineages.OrdinalComparison.CollectedAffineBandProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_phiMultiplicativeStepGap : LogicLineages.OrdinalComparison.Targets.PhiMultiplicativeStepGap :=
  LogicLineages.OrdinalComparison.phiMultiplicativeStepGap

theorem fixed_phiBetweenImagesRoot : LogicLineages.OrdinalComparison.Targets.PhiBetweenImagesRoot :=
  LogicLineages.OrdinalComparison.phiBetweenImagesRoot

theorem fixed_collectedAffineInputBand : LogicLineages.OrdinalComparison.Targets.CollectedAffineInputBand :=
  LogicLineages.OrdinalComparison.collectedAffineInputBand

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
