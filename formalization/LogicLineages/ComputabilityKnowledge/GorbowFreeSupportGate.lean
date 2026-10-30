module

public import LogicLineages.ComputabilityKnowledge.GorbowFreeSupportProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem gorbow_free_support : LogicLineages.ComputabilityKnowledge.Comparators.GorbowFreeSupport.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowFreeSupportProof.gorbowFreeSupport

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
