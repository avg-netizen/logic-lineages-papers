module

public import LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCode
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_boxCodeDigitIndex : Targets.boxCodeDigitIndex := BoxPolynomialCode.digit_index
theorem fixed_boxCodeMonomial : Targets.boxCodeMonomial := BoxPolynomialCode.monomial_calibration
theorem fixed_boxCodeRebase : Targets.boxCodeRebase := BoxPolynomialCode.rebase_calibration
theorem fixed_boxCodeBound : Targets.boxCodeBound := BoxPolynomialCode.bound
theorem fixed_boxCodeCoverage : Targets.boxCodeCoverage := BoxPolynomialCode.coverage

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
