module

public import LogicLineages.ComputabilityKnowledge.ExponentialIdentityProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem exponential_identity : LogicLineages.ComputabilityKnowledge.Comparators.ExponentialIdentity.Target :=
  LogicLineages.ComputabilityKnowledge.ExponentialIdentityProof.exponentialIdentity

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
