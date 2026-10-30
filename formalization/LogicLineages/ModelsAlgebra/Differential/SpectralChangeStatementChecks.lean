module

public import LogicLineages.ModelsAlgebra.Differential.SpectralChange
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralChangeInverse : Targets.spectralChangeInverse := SpectralChange.inverse
theorem fixed_spectralChangeCalibration : Targets.spectralChangeCalibration := SpectralChange.calibration
theorem fixed_spectralGenericJetIndependence : Targets.spectralGenericJetIndependence :=
  SpectralChange.generic_jet_independence

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
