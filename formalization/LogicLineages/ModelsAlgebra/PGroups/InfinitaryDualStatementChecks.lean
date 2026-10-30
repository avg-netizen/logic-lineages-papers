module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDual
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.InfinitaryDualStatementChecks

theorem fixed_dual_realization : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInfinitaryDualRealization :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.dual_realization

theorem fixed_dual_complexity : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInfinitaryDualComplexity :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.dual_complexity

end LogicLineages.ModelsAlgebra.PGroups.InfinitaryDualStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
