module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicTruthProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem fixed_gorbowAtomicTruth : LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicTruth.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowAtomicTruthProof.gorbowAtomicTruth

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
