module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicRankAssembly
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_finite_cyclic_ulm_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteCyclicUlmRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_cyclic_ulm_rank

theorem fixed_infinite_cyclic_ulm_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInfiniteCyclicUlmRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.infinite_cyclic_ulm_rank

theorem fixed_full_shift_ulm_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFullShiftUlmRank :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.full_shift_ulm_rank

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
