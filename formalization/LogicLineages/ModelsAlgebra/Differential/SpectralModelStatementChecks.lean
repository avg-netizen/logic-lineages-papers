module

public import LogicLineages.ModelsAlgebra.Differential.SpectralModel
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralModelVariablesIndependent : Targets.spectralModelVariablesIndependent :=
  SpectralModel.variables_independent
theorem fixed_spectralModelVariableDerivative : Targets.spectralModelVariableDerivative :=
  SpectralModel.variable_derivative
theorem fixed_spectralModelEquation : Targets.spectralModelEquation := SpectralModel.equation
theorem fixed_spectralModelCoordinateCalibration : Targets.spectralModelCoordinateCalibration :=
  SpectralModel.coordinates
theorem fixed_spectralModelGenericJets : Targets.spectralModelGenericJets := SpectralModel.generic_jets

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
