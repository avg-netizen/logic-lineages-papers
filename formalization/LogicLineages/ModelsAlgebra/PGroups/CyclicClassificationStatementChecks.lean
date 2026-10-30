module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicClassification
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_bounded_cyclic_calibrated_decomposition : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedCyclicCalibratedDecomposition :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_cyclic_calibrated_decomposition

theorem fixed_cyclic_root_sum_reindex : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCyclicRootSumReindex :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.cyclic_root_sum_reindex

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
