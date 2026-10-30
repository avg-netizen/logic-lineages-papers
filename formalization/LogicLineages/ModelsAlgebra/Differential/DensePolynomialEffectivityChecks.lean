module

public import LogicLineages.ModelsAlgebra.Differential.DensePolynomialEffectivity
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_densePolynomialArithmeticPrimitiveRecursive :
    Targets.densePolynomialArithmeticPrimitiveRecursive :=
  DensePolynomial.arithmetic_primitive_recursive

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
