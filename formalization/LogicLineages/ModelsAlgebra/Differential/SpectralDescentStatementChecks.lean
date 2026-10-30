module

public import LogicLineages.ModelsAlgebra.Differential.SpectralDescent
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralObstructionRationalDescent : Targets.spectralObstructionRationalDescent :=
  SpectralDescent.rational_descent

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
