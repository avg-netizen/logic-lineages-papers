module

public import LogicLineages.ComputabilityKnowledge.CircuitReductionEffectivityProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem circuit_reduction_effectivity : Comparators.CircuitReductionEffectivity.Target :=
  CircuitReductionEffectivityProof.circuitReductionEffectivity

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
