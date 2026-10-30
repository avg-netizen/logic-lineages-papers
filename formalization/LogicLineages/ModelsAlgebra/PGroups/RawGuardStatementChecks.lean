module

public import LogicLineages.ModelsAlgebra.PGroups.RawGuard
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_raw_guard_pi_realization : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawGuardPiRealization :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_guard_pi_realization

theorem fixed_raw_guard_difference_realization : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawGuardDifferenceRealization :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_guard_difference_realization

theorem fixed_raw_guard_pi_complexity : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawGuardPiComplexity :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_guard_pi_complexity

theorem fixed_raw_guard_difference_complexity : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawGuardDifferenceComplexity :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_guard_difference_complexity

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
