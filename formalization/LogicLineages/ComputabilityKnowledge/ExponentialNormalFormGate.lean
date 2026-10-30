module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem exponential_normal_form_algebra :
    Comparators.ExponentialNormalForm.Target := ExponentialNormalFormProof.normalFormAlgebra

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
