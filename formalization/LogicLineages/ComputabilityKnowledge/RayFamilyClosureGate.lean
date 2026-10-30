module

public import LogicLineages.ComputabilityKnowledge.RayFamilyClosureProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ray_family_closure : LogicLineages.ComputabilityKnowledge.Comparators.RayFamilyClosure.Target :=
  LogicLineages.ComputabilityKnowledge.RayFamilyClosureProof.rayFamilyClosure

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
