module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodecProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem exponential_normal_form_codec :
    Comparators.ExponentialNormalFormCodec.Target :=
  ExponentialNormalFormCodecProof.normalFormCodec

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
