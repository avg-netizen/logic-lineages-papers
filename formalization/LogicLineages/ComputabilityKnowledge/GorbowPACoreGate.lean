module

public import LogicLineages.ComputabilityKnowledge.GorbowPACoreProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem gorbow_pa_core : LogicLineages.ComputabilityKnowledge.Comparators.GorbowPACore.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowPACoreProof.gorbowPACore

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
