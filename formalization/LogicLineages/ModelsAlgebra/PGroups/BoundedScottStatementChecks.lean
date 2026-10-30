module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedScott
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_countable_ulm_table_exists : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCountableUlmTableExists :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.countable_ulm_table_exists

theorem fixed_bounded_pi_three_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupBoundedPiThreeScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.bounded_pi_three_scott

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
