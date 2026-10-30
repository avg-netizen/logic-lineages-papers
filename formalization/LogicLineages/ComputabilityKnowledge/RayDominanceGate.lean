module

public import LogicLineages.ComputabilityKnowledge.RayDominanceProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ray_numerical_dominance : Comparators.RayDominance.Target :=
  RayDominanceProof.rayDominance

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
