module

public import LogicLineages.ComputabilityKnowledge.GorbowTermPrefixCodeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem gorbow_term_prefix_code : LogicLineages.ComputabilityKnowledge.Comparators.GorbowTermPrefixCode.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowTermPrefixCodeProof.gorbowTermPrefixCode

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
