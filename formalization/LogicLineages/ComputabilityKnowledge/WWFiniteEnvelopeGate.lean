module

public import LogicLineages.ComputabilityKnowledge.WWFiniteEnvelopeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ww_finite_envelope : LogicLineages.ComputabilityKnowledge.Comparators.WWFiniteEnvelope.Target :=
  LogicLineages.ComputabilityKnowledge.WWFiniteEnvelopeProof.wwFiniteEnvelope

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
