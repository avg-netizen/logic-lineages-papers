module

public import LogicLineages.ModelsAlgebra.Differential.NumericDeterminantEffectivity
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_numericDeterminantPrimitiveRecursive : Targets.numericDeterminantPrimitiveRecursive :=
  NumericDeterminant.determinant_primitive_recursive

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
