module

public import LogicLineages.ComputabilityKnowledge.CircuitComparisonProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem circuit_comparison : Comparators.CircuitComparison.Target :=
  CircuitComparisonProof.circuitComparison

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
