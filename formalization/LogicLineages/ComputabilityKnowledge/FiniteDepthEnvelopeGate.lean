module

public import LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelopeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem finite_depth_envelope : Comparators.FiniteDepthEnvelope.Target :=
  FiniteDepthEnvelopeProof.finiteDepthEnvelope

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
