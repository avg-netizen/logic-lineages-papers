module

public import LogicLineages.ModelsAlgebra.PGroups.RawSourceOneInfinite
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_raw_source_positive_lower_scott_bounds : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawSourcePositiveLowerScottBounds :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_source_positive_lower_scott_bounds

theorem fixed_raw_source_zero_lower_scott_bounds : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawSourceZeroLowerScottBounds :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_source_zero_lower_scott_bounds

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
