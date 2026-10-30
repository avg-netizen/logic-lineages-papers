module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteStep
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_finite_step_finite_ulm : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteStepFiniteUlm :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_step_finite_ulm

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
