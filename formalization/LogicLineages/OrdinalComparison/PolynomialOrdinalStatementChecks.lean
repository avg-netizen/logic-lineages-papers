module
public import LogicLineages.OrdinalComparison.PolynomialOrdinalProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_polynomialRawNoteInjective : Targets.PolynomialRawNoteInjective := polynomialRawNoteInjective
theorem fixed_polynomialRawNoteOrdinalComplete : Targets.PolynomialRawNoteOrdinalComplete :=
  polynomialRawNoteOrdinalComplete

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
