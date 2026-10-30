module

public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_raw_isomorphism_additive : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawIsomorphismAdditive :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_isomorphism_additive

theorem fixed_raw_scott_restriction : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawScottRestriction :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_scott_restriction

theorem fixed_raw_difference_scott_restriction : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawDifferenceScottRestriction :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_difference_scott_restriction

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
