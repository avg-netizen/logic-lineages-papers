module

public import LogicLineages.ModelsAlgebra.PGroups.ProperCoset
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_proper_coset_sum_membership : LogicLineages.ModelsAlgebra.PGroups.Targets.groupProperCosetSumMembership :=
  LogicLineages.ModelsAlgebra.PGroups.proper_coset_sum_membership

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
