module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem exponential_normal_form_product :
    Comparators.ExponentialNormalFormProduct.Target :=
  ExponentialNormalFormProductProof.normalFormProduct

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
