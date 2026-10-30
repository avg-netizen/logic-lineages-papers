module

public import LogicLineages.ComputabilityKnowledge.GorbowBooleanTruthProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem fixed_gorbowBooleanTruth : LogicLineages.ComputabilityKnowledge.Comparators.GorbowBooleanTruth.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowBooleanTruthProof.gorbowBooleanTruth

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
