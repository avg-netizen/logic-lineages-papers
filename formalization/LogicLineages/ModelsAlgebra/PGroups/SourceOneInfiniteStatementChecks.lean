module

public import LogicLineages.ModelsAlgebra.PGroups.SourceOneInfinite
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_source_positive_lower_scott_bounds : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSourcePositiveLowerScottBounds :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.source_positive_lower_scott_bounds

theorem fixed_source_zero_lower_scott_bounds : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSourceZeroLowerScottBounds :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.source_zero_lower_scott_bounds

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
