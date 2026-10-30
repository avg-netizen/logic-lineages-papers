module

public import LogicLineages.ModelsAlgebra.Differential.MissingSpectralModel
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_missingSpectralModelEquation : Targets.missingSpectralModelEquation :=
  MissingSpectralModel.equation
theorem fixed_missingSpectralModelCoordinates : Targets.missingSpectralModelCoordinates :=
  MissingSpectralModel.coordinates
theorem fixed_missingSpectralModelCalibration : Targets.missingSpectralModelCalibration :=
  MissingSpectralModel.calibration
theorem fixed_missingSpectralModelObstructionZero : Targets.missingSpectralModelObstructionZero :=
  MissingSpectralModel.obstruction_zero
theorem fixed_missingSpectralModelAvoidance : Targets.missingSpectralModelAvoidance :=
  MissingSpectralModel.avoidance

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
