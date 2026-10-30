module

public import LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomialBounds
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_kroneckerPolynomialBoxExists : Targets.kroneckerPolynomialBoxExists :=
  KroneckerPolynomial.box_exists
theorem fixed_kroneckerPolynomialProductBox : Targets.kroneckerPolynomialProductBox :=
  KroneckerPolynomial.product_box
theorem fixed_kroneckerPolynomialQuotientBox : Targets.kroneckerPolynomialQuotientBox :=
  KroneckerPolynomial.quotient_box
theorem fixed_kroneckerPolynomialLargerBaseVerification : Targets.kroneckerPolynomialLargerBaseVerification :=
  KroneckerPolynomial.larger_base_verification

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
