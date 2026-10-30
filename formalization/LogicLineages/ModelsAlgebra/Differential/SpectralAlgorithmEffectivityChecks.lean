module

public import LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithmEffectivity
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralAlgorithmSearchTotal : Targets.spectralAlgorithmSearchTotal :=
  SpectralAlgorithm.search_total
theorem fixed_spectralAlgorithmSearchPartialRecursive : Targets.spectralAlgorithmSearchPartialRecursive :=
  SpectralAlgorithm.search_partial_recursive

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
