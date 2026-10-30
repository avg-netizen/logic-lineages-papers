module

public import LogicLineages.ComputabilityKnowledge.RayCoefficientCollectionProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ray_coefficient_collection : Comparators.RayCoefficientCollection.Target :=
  RayCoefficientCollectionProof.rayCoefficientCollection

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
