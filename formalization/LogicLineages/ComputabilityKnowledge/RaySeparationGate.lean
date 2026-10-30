module

public import LogicLineages.ComputabilityKnowledge.RaySeparationProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ray_separation : LogicLineages.ComputabilityKnowledge.Comparators.RaySeparation.Target :=
  LogicLineages.ComputabilityKnowledge.RaySeparationProof.raySeparation

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
