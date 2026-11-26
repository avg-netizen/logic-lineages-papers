module
public import LogicLineages.CartierObserverCurrent.LocalPolynomialProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Basic.LocalPolynomialStatementChecks

theorem fixed_localPolePolynomialRule : Targets.LocalPolePolynomialRule.{u} :=
  LocalPolynomial.localPolePolynomialRule

#audit_namespace LogicLineages.CartierObserverCurrent.Basic.LocalPolynomialStatementChecks
end LogicLineages.CartierObserverCurrent.Basic.LocalPolynomialStatementChecks
