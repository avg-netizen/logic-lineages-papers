module

public import LogicLineages.ComputabilityKnowledge.PolynomialComparisonProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem polynomial_comparison : Comparators.PolynomialComparison.Target :=
  PolynomialComparisonProof.polynomialComparison

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
