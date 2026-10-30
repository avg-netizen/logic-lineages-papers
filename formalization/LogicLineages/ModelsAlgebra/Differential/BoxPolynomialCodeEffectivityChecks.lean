module

public import LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCodeEffectivity
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_boxCodeOperationsPrimitiveRecursive : Targets.boxCodeOperationsPrimitiveRecursive :=
  BoxPolynomialCode.operations_primitive_recursive

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
