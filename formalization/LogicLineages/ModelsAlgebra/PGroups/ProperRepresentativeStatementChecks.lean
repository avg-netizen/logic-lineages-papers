module

public import LogicLineages.ModelsAlgebra.PGroups.ProperRepresentative
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_proper_representative : LogicLineages.ModelsAlgebra.PGroups.Targets.groupProperRepresentative :=
  LogicLineages.ModelsAlgebra.PGroups.proper_representative

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
