module

public import LogicLineages.ModelsAlgebra.PGroups.TrivialScott
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.TrivialScottStatementChecks

theorem fixed_trivial_pi_one_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTrivialPiOneScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.trivial_pi_one_scott

end LogicLineages.ModelsAlgebra.PGroups.TrivialScottStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
