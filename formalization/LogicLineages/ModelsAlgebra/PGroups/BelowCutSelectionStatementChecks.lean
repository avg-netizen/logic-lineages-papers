module

public import LogicLineages.ModelsAlgebra.PGroups.BelowCutSelection
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_below_cut_selection : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBelowCutSelection :=
  LogicLineages.ModelsAlgebra.PGroups.below_cut_selection

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
