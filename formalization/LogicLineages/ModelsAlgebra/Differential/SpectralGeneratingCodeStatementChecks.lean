module

public import LogicLineages.ModelsAlgebra.Differential.SpectralGeneratingCode
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralGeneratingCodeCorrect : Targets.spectralGeneratingCodeCorrect :=
  SpectralResultantCode.generating_correct

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
