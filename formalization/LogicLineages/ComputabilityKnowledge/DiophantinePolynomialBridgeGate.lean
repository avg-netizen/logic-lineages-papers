module

public import LogicLineages.ComputabilityKnowledge.DiophantinePolynomialBridgeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem diophantine_polynomial_bridge : Comparators.DiophantinePolynomialBridge.Target :=
  DiophantinePolynomialBridgeProof.diophantinePolynomialBridge

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
