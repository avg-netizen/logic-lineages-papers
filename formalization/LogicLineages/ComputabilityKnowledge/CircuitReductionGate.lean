module

public import LogicLineages.ComputabilityKnowledge.CircuitReductionProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem circuit_reduction : Comparators.CircuitReduction.Target :=
  CircuitReductionProof.circuitReduction

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
