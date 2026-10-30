module

public import LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithmInputs
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralAlgorithmInputCoverage : Targets.spectralAlgorithmInputCoverage :=
  SpectralAlgorithm.input_coverage
theorem fixed_spectralAlgorithmOrder : Targets.spectralAlgorithmOrder := SpectralAlgorithm.order_correct

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
