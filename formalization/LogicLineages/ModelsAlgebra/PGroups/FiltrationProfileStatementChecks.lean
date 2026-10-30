module

public import LogicLineages.ModelsAlgebra.PGroups.FiltrationProfile
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_filtration_profile_total : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiltrationProfileTotal :=
  LogicLineages.ModelsAlgebra.PGroups.filtration_profile_total

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
