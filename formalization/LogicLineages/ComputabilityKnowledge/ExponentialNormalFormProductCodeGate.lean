module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductCodeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem exponential_normal_form_product_code :
    Comparators.ExponentialNormalFormProductCode.Target :=
  ExponentialNormalFormProductCodeProof.productCode

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
