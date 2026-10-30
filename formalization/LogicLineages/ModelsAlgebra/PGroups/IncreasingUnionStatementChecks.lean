module

public import LogicLineages.ModelsAlgebra.PGroups.IncreasingUnion
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.IncreasingUnionStatementChecks

theorem fixed_embedding_low_sigma_ascent : LogicLineages.ModelsAlgebra.PGroups.Targets.groupEmbeddingLowSigmaAscent :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.embedding_low_sigma_ascent

theorem fixed_increasing_tuple_containment : LogicLineages.ModelsAlgebra.PGroups.Targets.groupIncreasingTupleContainment :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.increasing_tuple_containment

theorem fixed_increasing_pi_two_preservation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupIncreasingPiTwoPreservation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.increasing_pi_two_preservation

end LogicLineages.ModelsAlgebra.PGroups.IncreasingUnionStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
