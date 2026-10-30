module

public import LogicLineages.ModelsAlgebra.PGroups.OneInfiniteBounds
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_positive_lower_scott_bounds : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPositiveLowerScottBounds :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.positive_lower_scott_bounds

theorem fixed_zero_lower_scott_bounds : LogicLineages.ModelsAlgebra.PGroups.Targets.groupZeroLowerScottBounds :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.zero_lower_scott_bounds

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
