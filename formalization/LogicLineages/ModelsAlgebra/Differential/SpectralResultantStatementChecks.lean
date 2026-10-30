module

public import LogicLineages.ModelsAlgebra.Differential.SpectralResultant
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralResultantCalibration : Targets.spectralResultantCalibration :=
  SpectralResultant.resultant_calibration
theorem fixed_spectralResultantBox : Targets.spectralResultantBox := SpectralResultant.resultant_box

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
