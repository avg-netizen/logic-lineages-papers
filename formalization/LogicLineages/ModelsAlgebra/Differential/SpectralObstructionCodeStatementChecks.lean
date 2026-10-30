module

public import LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralObstructionCodeCorrect : Targets.spectralObstructionCodeCorrect :=
  SpectralResultantCode.obstruction_correct

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
