module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrap
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrapStatementChecks

theorem fixed_sigma_wrap_realization : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSigmaWrapRealization :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.sigma_wrap_realization

theorem fixed_pi_wrap_realization : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPiWrapRealization :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.pi_wrap_realization

theorem fixed_sigma_wrap_complexity : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSigmaWrapComplexity :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.sigma_wrap_complexity

theorem fixed_pi_wrap_complexity : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPiWrapComplexity :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.pi_wrap_complexity

end LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrapStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
