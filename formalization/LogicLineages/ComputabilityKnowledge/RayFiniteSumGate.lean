module

public import LogicLineages.ComputabilityKnowledge.RayFiniteSumProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ray_actual_finite_sum : Comparators.RayFiniteSum.Target :=
  RayFiniteSumProof.rayFiniteSum

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
