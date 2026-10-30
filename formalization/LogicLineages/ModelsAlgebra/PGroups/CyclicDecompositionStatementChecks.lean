module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicDecomposition
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_cyclic_root_sum_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicRootSumInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_root_sum_injective

theorem fixed_cyclic_root_sum_surjective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicRootSumSurjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_root_sum_surjective

theorem fixed_bounded_cyclic_decomposition : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedCyclicDecomposition :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_cyclic_decomposition

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
