module

public import LogicLineages.ComputabilityKnowledge.RayStableMaximumProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ray_stable_greatest_key : Comparators.RayStableMaximum.Target :=
  RayStableMaximumProof.rayStableMaximum

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
