module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem exponential_normalization :
    Comparators.ExponentialNormalizer.Target :=
  ExponentialNormalizerProof.sourceNormalization

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
