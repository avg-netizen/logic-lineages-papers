module

public import LogicLineages.ModelsAlgebra.PGroups.QuotientExactLength
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_quotient_exact_length : LogicLineages.ModelsAlgebra.PGroups.Targets.groupQuotientExactLength :=
  LogicLineages.ModelsAlgebra.PGroups.quotient_exact_length

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
