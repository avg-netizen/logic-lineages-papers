module

public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryQuotient
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_p_primary_quotient : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPPrimaryQuotient :=
  LogicLineages.ModelsAlgebra.PGroups.p_primary_quotient

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
