module

public import LogicLineages.ComputabilityKnowledge.PolynomialDomainShiftProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem polynomial_domain_shift : Comparators.PolynomialDomainShift.Target :=
  PolynomialDomainShiftProof.polynomialDomainShift

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
