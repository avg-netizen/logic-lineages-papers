module
public import LogicLineages.CartierObserverCurrent.F2DescentProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.F2Descent.StatementChecks

theorem fixed_polynomialDescent : Targets.PolynomialDescent :=
  LogicLineages.CartierObserverCurrent.F2Descent.polynomialDescent

theorem fixed_rationalDescent : Targets.RationalDescent :=
  LogicLineages.CartierObserverCurrent.F2Descent.rationalDescent

#audit_namespace LogicLineages.CartierObserverCurrent.F2Descent.StatementChecks
end LogicLineages.CartierObserverCurrent.F2Descent.StatementChecks
