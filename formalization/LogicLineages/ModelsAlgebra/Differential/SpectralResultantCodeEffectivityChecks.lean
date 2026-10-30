module

public import LogicLineages.ModelsAlgebra.Differential.SpectralResultantCodeEffectivity
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_spectralResultantCodePrimitiveRecursive : Targets.spectralResultantCodePrimitiveRecursive :=
  SpectralResultantCode.operations_primitive_recursive

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
