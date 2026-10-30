module

public import LogicLineages.ModelsAlgebra.PGroups.QuotientHeight
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_quotient_membership_reflection : LogicLineages.ModelsAlgebra.PGroups.Targets.groupQuotientMembershipReflection :=
  LogicLineages.ModelsAlgebra.PGroups.quotient_membership_reflection

theorem fixed_quotient_successor_height_reflection : LogicLineages.ModelsAlgebra.PGroups.Targets.groupQuotientSuccessorHeightReflection :=
  LogicLineages.ModelsAlgebra.PGroups.quotient_successor_height_reflection

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
