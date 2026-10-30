module

public import LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomial
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_kroneckerPolynomialMonomial : Targets.kroneckerPolynomialMonomial :=
  KroneckerPolynomial.monomial_encoding
theorem fixed_kroneckerPolynomialCoefficient : Targets.kroneckerPolynomialCoefficient :=
  KroneckerPolynomial.coefficient_calibration
theorem fixed_kroneckerPolynomialDegreeBound : Targets.kroneckerPolynomialDegreeBound :=
  KroneckerPolynomial.degree_bound
theorem fixed_kroneckerPolynomialInjective : Targets.kroneckerPolynomialInjective :=
  KroneckerPolynomial.polynomial_injective
theorem fixed_kroneckerDecodedBox : Targets.kroneckerDecodedBox := KroneckerPolynomial.decoded_box
theorem fixed_kroneckerPolynomialDecodeEncode : Targets.kroneckerPolynomialDecodeEncode :=
  KroneckerPolynomial.decode_encode
theorem fixed_kroneckerPolynomialEncodeDecode : Targets.kroneckerPolynomialEncodeDecode :=
  KroneckerPolynomial.encode_decode

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
