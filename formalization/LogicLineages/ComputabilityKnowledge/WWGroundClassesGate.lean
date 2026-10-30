module

public import LogicLineages.ComputabilityKnowledge.WWGroundClassesProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ww_ground_classes : LogicLineages.ComputabilityKnowledge.Comparators.WWGroundClasses.Target :=
  LogicLineages.ComputabilityKnowledge.WWGroundClassesProof.wwGroundClasses

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
