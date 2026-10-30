module

public import LogicLineages.ModelsAlgebra.Differential.SpectralOuterCode
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralOuterCodeArithmetic : Targets.spectralOuterCodeArithmetic :=
  SpectralResultantCode.outer_arithmetic

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
