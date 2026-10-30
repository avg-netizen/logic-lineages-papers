module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperationsProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem exponential_normal_form_code_operations :
    Comparators.ExponentialNormalFormCodeOperations.Target :=
  ExponentialNormalFormCodeOperationsProof.codeOperations

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
