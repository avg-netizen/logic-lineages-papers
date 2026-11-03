module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherenceProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherence.StatementChecks

theorem fullInternalCoherence : Targets.Target := Proof.fullTarget
theorem openTermCongruence : Targets.OpenTermCongruence := fullInternalCoherence.1
theorem conditionalTermCongruence : Targets.ConditionalTermCongruence := fullInternalCoherence.2.1
theorem registryCoherence : Targets.RegistryCoherence := fullInternalCoherence.2.2.1
theorem namedRegistryCoherence : Targets.NamedRegistryCoherence := fullInternalCoherence.2.2.2.1
theorem concreteDuplicate : Targets.ConcreteDuplicate := fullInternalCoherence.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherence.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherence
