module

public import LogicLineages.ModelsAlgebra.Differential.SpectralSylvesterCode
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralSylvesterCodeCorrect : Targets.spectralSylvesterCodeCorrect :=
  SpectralResultantCode.sylvester_correct

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
