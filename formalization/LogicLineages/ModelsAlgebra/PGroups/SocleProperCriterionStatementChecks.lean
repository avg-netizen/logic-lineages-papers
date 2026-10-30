module

public import LogicLineages.ModelsAlgebra.PGroups.SocleProperCriterion
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_socle_proper_criterion : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleProperCriterion :=
  LogicLineages.ModelsAlgebra.PGroups.socle_proper_criterion

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
