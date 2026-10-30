module

public import LogicLineages.ComputabilityKnowledge.WWOrdinalPrefixCodeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ww_ordinal_prefix_code : LogicLineages.ComputabilityKnowledge.Comparators.WWOrdinalPrefixCode.Target :=
  LogicLineages.ComputabilityKnowledge.WWOrdinalPrefixCodeProof.wwOrdinalPrefixCode

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
