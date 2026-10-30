module

public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearch
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_polynomialCodeDegreeCorrect : Targets.polynomialCodeDegreeCorrect :=
  PolynomialCertificateSearch.degree_correct
theorem fixed_polynomialCertificateVerifierCorrect : Targets.polynomialCertificateVerifierCorrect :=
  PolynomialCertificateSearch.verifier_correct
theorem fixed_polynomialCertificateExists : Targets.polynomialCertificateExists :=
  PolynomialCertificateSearch.certificate_exists
theorem fixed_polynomialSearchAnswerCorrect : Targets.polynomialSearchAnswerCorrect :=
  PolynomialCertificateSearch.search_answer_correct
theorem fixed_polynomialSearchTotal : Targets.polynomialSearchTotal :=
  PolynomialCertificateSearch.search_total

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
