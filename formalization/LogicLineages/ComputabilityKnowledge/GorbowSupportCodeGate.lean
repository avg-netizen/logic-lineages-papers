module

public import LogicLineages.ComputabilityKnowledge.GorbowSupportCodeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem gorbow_support_code : LogicLineages.ComputabilityKnowledge.Comparators.GorbowSupportCode.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowSupportCodeProof.gorbowSupportCode

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
