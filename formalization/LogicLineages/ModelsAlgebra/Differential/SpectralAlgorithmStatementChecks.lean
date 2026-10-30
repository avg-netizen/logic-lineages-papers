module

public import LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithmComplete
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralAlgorithmSearchCorrect : Targets.spectralAlgorithmSearchCorrect :=
  SpectralAlgorithm.search_correct
theorem fixed_spectralAlgorithmComputableRealization : Targets.spectralAlgorithmComputableRealization :=
  SpectralAlgorithm.computable_realization

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
