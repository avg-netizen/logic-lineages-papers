module

public import LogicLineages.ComputabilityKnowledge.GorbowSelectedCodeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem fixed_gorbowSelectedCode : LogicLineages.ComputabilityKnowledge.Comparators.GorbowSelectedCode.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowSelectedCodeProof.gorbowSelectedCode

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
