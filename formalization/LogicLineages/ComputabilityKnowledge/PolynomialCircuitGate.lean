module

public import LogicLineages.ComputabilityKnowledge.PolynomialCircuitProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem polynomial_circuit : Comparators.PolynomialCircuit.Target :=
  PolynomialCircuitProof.polynomialCircuit

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
