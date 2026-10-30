module

public import LogicLineages.ModelsAlgebra.PGroups.UniversalScott
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.UniversalScottStatementChecks

theorem fixed_universal_no_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUniversalNoScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.universal_no_scott

end LogicLineages.ModelsAlgebra.PGroups.UniversalScottStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
