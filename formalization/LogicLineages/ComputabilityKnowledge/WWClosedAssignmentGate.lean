module

public import LogicLineages.ComputabilityKnowledge.WWClosedAssignmentProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ww_closed_assignment : LogicLineages.ComputabilityKnowledge.Comparators.WWClosedAssignment.Target :=
  LogicLineages.ComputabilityKnowledge.WWClosedAssignmentProof.wwClosedAssignment

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
