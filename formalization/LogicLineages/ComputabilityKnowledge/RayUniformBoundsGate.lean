module

public import LogicLineages.ComputabilityKnowledge.RayUniformBoundsProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ray_uniform_bounds : Comparators.RayUniformBounds.Target :=
  RayUniformBoundsProof.rayUniformBounds

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
