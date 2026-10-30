module

public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCodeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem gorbow_instance_code : LogicLineages.ComputabilityKnowledge.Comparators.GorbowInstanceCode.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowInstanceCodeProof.gorbowInstanceCode

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
