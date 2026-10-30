module

public import LogicLineages.ModelsAlgebra.Differential.DensePolynomial
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_densePolynomialCoverage : Targets.densePolynomialCoverage := DensePolynomial.coverage
theorem fixed_densePolynomialCoefficients : Targets.densePolynomialCoefficients :=
  DensePolynomial.coefficients
theorem fixed_densePolynomialArithmeticCorrect : Targets.densePolynomialArithmeticCorrect :=
  DensePolynomial.arithmetic_correct

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
