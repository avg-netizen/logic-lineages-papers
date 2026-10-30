module

public import LogicLineages.ModelsAlgebra.PGroups.ResidualCyclic
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_residual_cyclic_exponent : LogicLineages.ModelsAlgebra.PGroups.Targets.groupResidualCyclicExponent :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.residual_cyclic_exponent

theorem fixed_residual_cyclic_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupResidualCyclicRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.residual_cyclic_rank

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
