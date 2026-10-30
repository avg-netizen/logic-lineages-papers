module

public import LogicLineages.ModelsAlgebra.PGroups.FreshCombine
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_fresh_combine_odd : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFreshCombineOdd :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.fresh_combine_odd

theorem fixed_fresh_combine_even : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFreshCombineEven :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.fresh_combine_even

theorem fixed_fresh_combine_injective : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFreshCombineInjective :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.fresh_combine_injective

theorem fixed_fresh_combine_fixes : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFreshCombineFixes :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.fresh_combine_fixes

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
