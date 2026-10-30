module

public import LogicLineages.ModelsAlgebra.Differential.SpectralGenerating
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralGeneratingDegree : Targets.spectralGeneratingDegree :=
  SpectralResultant.generating_degree
theorem fixed_spectralGeneratingRootCalibration : Targets.spectralGeneratingRootCalibration :=
  SpectralResultant.generating_root_calibration

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
