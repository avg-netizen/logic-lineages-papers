module

public import LogicLineages.ComputabilityKnowledge.RestrictedProductProof
public meta import LogicLineages.Audit

@[expose] public section

/-! Independent exact statement gate, frozen before proof authoring. -/
namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem restricted_product : Comparators.RestrictedProduct.Target :=
  RestrictedProductProof.boundedMultiplication

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
