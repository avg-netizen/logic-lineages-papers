module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgramProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem exponential_effective_normalization :
    Comparators.ExponentialNormalizerProgram.Target :=
  ExponentialNormalizerProgramProof.effectiveNormalization

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
