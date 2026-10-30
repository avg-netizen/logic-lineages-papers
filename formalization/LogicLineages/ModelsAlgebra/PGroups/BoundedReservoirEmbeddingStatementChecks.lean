module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedReservoirEmbedding
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_bounded_reservoir_embedding : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedReservoirEmbedding :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_reservoir_embedding

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
