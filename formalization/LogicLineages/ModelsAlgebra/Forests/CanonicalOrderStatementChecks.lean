module

public import LogicLineages.ModelsAlgebra.Forests.CanonicalOrderProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem canonicalPartialOrderLaws : Targets.CanonicalPartialOrderLaws :=
  CanonicalOrderProof.canonicalPartialOrderLaws

theorem canonicalPredecessorsChain : Targets.CanonicalPredecessorsChain :=
  CanonicalOrderProof.canonicalPredecessorsChain

theorem canonicalAdjacencyComparability : Targets.CanonicalAdjacencyComparability :=
  CanonicalOrderProof.canonicalAdjacencyComparability

theorem canonicalGraphRepresentation : Targets.CanonicalGraphRepresentation :=
  CanonicalOrderProof.canonicalGraphRepresentation

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
