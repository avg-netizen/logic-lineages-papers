module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedBindingProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem fixed_gorbowNamedBinding : LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedBinding.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowNamedBindingProof.gorbowNamedBinding

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
