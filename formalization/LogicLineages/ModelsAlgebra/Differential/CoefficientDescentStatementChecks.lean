module

public import LogicLineages.ModelsAlgebra.Differential.CoefficientDescent
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_mvPolynomialDivisibilityDescent : Targets.mvPolynomialDivisibilityDescent :=
  CoefficientDescent.divisibility_descent

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
