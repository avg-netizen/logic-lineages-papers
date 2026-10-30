module

public import LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodecProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem exponential_hereditary_codec :
    Comparators.ExponentialHereditaryCodec.Target :=
  ExponentialHereditaryCodecProof.hereditaryCodec

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
