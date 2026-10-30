module

public import LogicLineages.ComputabilityKnowledge.RaySurvivingDifferenceProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ray_actual_surviving_difference : Comparators.RaySurvivingDifference.Target :=
  RaySurvivingDifferenceProof.raySurvivingDifference

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
