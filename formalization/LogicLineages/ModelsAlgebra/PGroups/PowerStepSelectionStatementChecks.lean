module

public import LogicLineages.ModelsAlgebra.PGroups.PowerStepSelection
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_power_step_selection : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPowerStepSelection :=
  LogicLineages.ModelsAlgebra.PGroups.power_step_selection

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
