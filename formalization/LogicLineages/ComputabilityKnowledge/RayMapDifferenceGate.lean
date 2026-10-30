module

public import LogicLineages.ComputabilityKnowledge.RayMapDifferenceProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ray_actual_map_difference : Comparators.RayMapDifference.Target :=
  RayMapDifferenceProof.rayMapDifference

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
