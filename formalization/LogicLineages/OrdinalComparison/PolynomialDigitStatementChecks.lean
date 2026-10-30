module
public import LogicLineages.OrdinalComparison.PolynomialDigitProof
public meta import LogicLineages.Audit

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualBinaryPolynomialDigitCoefficient : Targets.ActualBinaryPolynomialDigitCoefficient.{u} :=
  actualBinaryPolynomialDigitCoefficient
theorem fixed_actualBinaryPolynomialDigitSeries : Targets.ActualBinaryPolynomialDigitSeries.{u} := actualBinaryPolynomialDigitSeries
theorem fixed_actualBinaryPolynomialStepDegree : Targets.ActualBinaryPolynomialStepDegree.{u} := actualBinaryPolynomialStepDegree

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
