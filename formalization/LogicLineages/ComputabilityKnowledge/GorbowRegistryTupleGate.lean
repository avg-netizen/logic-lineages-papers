module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem fixed_gorbowRegistryTuple : LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryTuple.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof.gorbowRegistryTuple

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
